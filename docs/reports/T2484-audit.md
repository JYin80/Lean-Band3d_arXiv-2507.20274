Auditor model: claude-opus-5-5

# T2484 audit, round 1 (U4s2a: `Chain/IniTermIIGen.lean`, targets 1-4 and their part of 10-11), Tue Oct 13 03:40 UTC 2026
Inputs: ticket `docs/tickets/T2484.md`; prove report `docs/reports/T2484-prove.md` (sections (b)-(d)); 1a-audit `docs/reports/T2484-1a-audit.md` (split confirmed; target 1 text fixed = probe `T2484_KerFacts`, check text + E1).
Audit worktree `../RBM3D-wt/T2484-audit1`, detached at `t/T2484` 8162591d; build cache cloned with `cp -c`. Scratch: scratchpad `T2484/audit/` (`blk.py`, `aud.lean`; not committed). Under the split, U4s2b (targets 5-9) is not part of this audit.

## 1. Diff and layering
```
$ git diff --name-status main...t/T2484
A	RBM3D/Chain/IniTermIIGen.lean        (1113 lines; stop line 2,000)
A	RBM3D/Probe/T2484Pins.lean           (probe, on t/T2484 only, never merged)
M	RBM3D/Test/Axioms.lean               (1 line: owner text of STIniTermIIgL, :212)
$ git diff main...t/T2484 -- RBM3D/Induction RBM3D/Evolution RBM3D/BA RBM3D/Chain/{Carrier,Step2Gen,GridDuhamelGen,Step5Gen,
    Step5CasesGen,Step5KerGen,CltGen,ZeroModeGen,Step34Gen}.lean RBM3D.lean | wc -l        (G1, target 11)
       0
$ grep -n '^import RBM3D.BA' RBM3D/Chain/IniTermIIGen.lean          -> (no output)
$ git grep -n "import RBM3D.Chain.IniTermIIGen" HEAD               -> (no output; 0 importers)
$ git merge-tree --write-tree main t/T2484                          -> no conflict (main 5a060d90)
```
Imports: `Chain.Step5CasesGen`, `Chain.Step5KerGen`, `Chain.CltGen`, `Induction.IniTermII`, `Evolution.CltResolvent` (no BA, no U4s3/U5/V file).

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Chain.IniTermIIGen      (03:36:36 -> 03:36:49 UTC; olean written 03:36, absent from the main cache)
Build completed successfully (3790 jobs).
$ lake build RBM3D.Test.Axioms             -> Build completed successfully (2 jobs).
$ lake env lean scratchpad/T2484/audit/aud.lean    -> exit 0, error lines 0   (§3; #print axioms lines:)
  'RBM.BA.IniTermGen_KerFacts' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RBM.BA.iniTermGen_kerFacts_band' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RBM.BA.iniTermIIGen_core' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RBM.BA.iniTermIIGen_core_same' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RBM.BA.iniTermIIGen_concl' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RBM.BA.stIniTermIIgL_of' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RBM.BA.iniTermIIGen_band_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RBM.BA.IniTermIIGen_Theta_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RBM.BA.IniTermIIGen_UN_rep' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RBM.BA.IniTermIIGen_row_le' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RBM.BA.IniTermIIGen_cmp_pos'' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" RBM3D/Chain/IniTermIIGen.lean   -> (no output)
$ lake env lean docs/tickets/checks/T2484-check.lean   (on the branch)  -> exit 0, error lines 0
```
The full `lake build` with `#assert_rbm_axioms` is left to the hub at merge.

## 3. Statements against the pins (script diff + compiled equalities)
```
$ python3 -E blk.py <file> '^def IniTermGen_KerFacts' ... ; diff (one conjunct per line, names normalised to KF)
== target 1 (file) vs 1a-audit text (probe def T2484_KerFacts, probe:33-51)
identical
== target 1 (file) vs check T2484_KerFacts
11d10
<  (∀ (n : ℕ) (t : ℝ), 0 ≤ t → t < 1 → ∀ σ : Bool, STThg (mk sz z) n σ (!σ) t = STThg (mk sz z) n (!σ) σ t)
   (= E1, added and fixed at the 1a-audit, 1a-audit §2)
== target 4 file:
theorem stIniTermIIgL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ...) (mk : ...) (T0 : ...) (gK : ...) :
  Step5CasesGen_FlowFacts d Flow mk T0 → KF d Flow mk gK → STIniTermIIgL d law Flow mk T0
== target 4 check:
def T2484_IniTermIIOf : Prop := ∀ (d : ℕ) (law : ...) (Flow : ...) (mk : ...) (T0 : ...) (gK : ...),
  Step5CasesGen_FlowFacts d Flow mk T0 → KF d Flow mk gK → STIniTermIIgL d law Flow mk T0
```
(binder lists identical in the script output; abbreviated here.) Auditor's scratch `aud.lean` = the check file verbatim plus `import RBM3D.Chain.IniTermIIGen`, one `open` line, and these appended declarations, all compiled (exit 0):
```
def Aud_KerFacts ... := <probe:33-51 verbatim>
example : ∀ d Flow mk gK, IniTermGen_KerFacts d Flow mk gK = Aud_KerFacts d Flow mk gK := fun _ _ _ _ => rfl
example : ∀ d Flow mk gK, IniTermGen_KerFacts d Flow mk gK → T2484_KerFacts d Flow mk gK      -- target 1 ⇒ check default
def Aud_IniTermIIOf : Prop := <T2484_IniTermIIOf with T2484_KerFacts := Aud_KerFacts>
example : Aud_IniTermIIOf := stIniTermIIgL_of                                                 -- binding pin, target 4
example (d : ℕ) : IniTermGen_KerFacts d (fun sz κ ε 𝔠 𝔡 z => sz.STFlow κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z))
    (fun sz _ => sz.lam) := iniTermGen_kerFacts_band d
example (d : ℕ) : STIniTermII d := iniTermIIGen_band_holds d       -- same type as RBM.Gauss.Sizes.stIniTermII_holds
```
- **Target 1** (`IniTermGen_KerFacts`): definitionally equal to the 1a-audit text. Fields: `Step2Gen_USemigroup`; `Step5KerGen_ThDecay` at `gK`; R1 `0 ≤ gK·lam ∧ gK² ≤ lam² ∧ lam² ≤ A gK²`; E1; then, guarded by `0 < gK n ≤ 𝔡⁻¹`, the mixed column sum, the mixed zero mode and the same-charge short range of `STThg` at `gK`. Constants are fixed before `sz`, as in D1. No shift field (as in the ticket). **PASS.**
- **Target 2** (shape not binding, fixed in 1a (iii)). `iniTermIIGen_core` / `_core_same` keep the band `iniTermII_core` (IniTermII:1051) / `_core_same` (:1378) conclusions and losses term for term. Those are the `tailT … u` profile, `(1-s)/(1-u)·W^{-D}` (mixed, `Q = {0}`) and `W^{-D}` (same). The kernel is `Step2Gen_UN (mk sz z) n`. `g` → `sz.lam n`. `0 < g ≤ Λ` → the guard `0 < gK n ≤ 𝔡⁻¹`. `|E| ≤ 2, κm ≤ Im mE` → `Flow`. The regime is `1 - s ≤ lam²/L²`. **PASS.**
- **Target 3** (`iniTermIIGen_concl`): premises `FlowFacts`, target 1, `3 ≤ d`, `0 < κ`, `Flow`, `0 ≤ s`, `t ≤ T0`, `STReg5II`, `STDecaygL … s`. The conclusion is the two `STIniTermConclgL` conjuncts (`{0}`/`STSigMixed`, `∅`/`STSigSame`), as the ticket says. **PASS.**
- **Target 4** (`stIniTermIIgL_of`): equal to the binding pin, with the class fixed at the 1a-audit; head `STIniTermIIgL`. `STIngR5gL`'s order is kept: fixed `κ ε 𝔡 Cd`, then `∃ 𝔠d ∈ (0, 1/100]`, then `∀ 𝔠 sz z`. The pin fits `ST_step5_caseII_of_pinsgL` (`#check` in the scratch file). **PASS.**

## 4. Vacuity, hidden hypotheses, cycles
- The new hypothesis class is the one Prop `def IniTermGen_KerFacts`. No structure was introduced, so no field is hidden.
- Its band discharge `iniTermGen_kerFacts_band` compiles at `STFlow` (a nonempty flow: `flow_zB` is used in the §5 instances). The BA discharge is owed to U4-BA (a); the BA sources were checked at the 1a-audit (§2, `audit_E1_baFM` compiled).
- The class is not an external input: `iniTermGen_kerFacts_band` derives it from merged band results. So no TEAM §8 l.14 limit check applies.
- No cycle: the file imports only merged files, and nothing imports it.
- The proof of target 4 uses only `hR`, `hDec`, the flow and the two classes. The other `STIngR5gL` premises are discarded (`_`), which is allowed: they are premises of the merged pin.
- Ticket hypothesis rules:
```
X1-C1 hit lines: 40 88-153 187 1005-1008 1018-1099
  40, 187: docstrings; 88-153: private band helpers IniTermIIGen_flow_E/_mixed/_ck_pos (:89,:94,:100) + band discharge
  iniTermGen_kerFacts_band (:107); 1005-1008: band re-derivation iniTermIIGen_band_holds; 1018-1099: instances. No generic hit.
U-C4  grep -nE "^(noncomputable )?def"       -> 68:def IniTermGen_KerFacts ... : Prop   (no matrix/tensor def)
TN-C4 STGridRepNgL|ST_gridMart_of_repN        -> (no output)
X1-C4 (def|abbrev|structure) <13 pin names>   -> (no output)
UBA-C1 withLam                                -> (no output)
public decls: IniTermGen_KerFacts iniTermGen_kerFacts_band IniTermIIGen_Theta_eq IniTermIIGen_UN_rep IniTermIIGen_row_le
  iniTermIIGen_core iniTermIIGen_core_same IniTermIIGen_cmp_pos' iniTermIIGen_concl stIniTermIIgL_of iniTermIIGen_band_holds
  (pinned, or under the file stem, §3 (E)); 13 private
git grep -wF <each public name> main(5a060d90) -- RBM3D  -> 0 hits for all 11
```

## 5. Compiled nonempty instances (in the file, §7, lines 1013-1110; all compile in the module build of §2)
Data: `d = 3`, `szB` (`L = 4`, `W_n = n+4`, `lam = 1`), `zB = 1/2 + i/64`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`.
- **Target 1 (:1017).** The class at `szB`/`zB` through `flow_zB`. The guarded fields are taken at `n = 0` (`0 < 1 ≤ 10`), `t = 1/2`, and the column sum equals `2`.
- **Target 2, mixed (:1043) and same (:1063).** `n = 0`, `W = D = 2`, `(s,u) = (15/16, 31/32)`, `M = lam = 1`, `σ = (+,-)` or `(+,+)`. The tensor `X` is nonzero (the profile at `s`, attained). Every premise is discharged, including the regime `1-s = lam²/L²`.
- **Target 3 (:1084).** At `(szB, zB, 15/16, 31/32)`, `STReg5II` is discharged by `szB_reg5II`. Only `STDecaygL` at `s` stays a hypothesis; it is a Steps 1-2 carrier pin (another gate's pin).
- **Target 4 (:1095, :1104).**
  - The pin is applied at the band tuple, with both hypotheses discharged by `step5CasesGen_flowFacts_band` and `iniTermGen_kerFacts_band`. It is then fed to `inst_iniTermII` (Step5Pins:982).
  - The result is `InstIng5Concl … szB zB (15/16) (31/32) Cd` for every `Cd > 0`.
  - Every deterministic premise is discharged, through `inst_ing5_II` (Step5Pins:568-574): flow, window, `t ≤ lemT`, regime, and `STConStInd` eventually via `conStInd_const`.
  - The stochastic Steps 1-4 premises stay as premises of `InstIng5Concl`.
- `iniTermIIGen_band_holds` re-derives `stIniTermII_holds` (same type, §3).
None of these is degenerate: no `N = 0`, no empty index set, no collapsed window, no `False` premise. Every constant is small.

## 6. Paper deltas
- `T2484a` (the initial terms over the carrier, with the column sum, zero mode and short range as carrier data at `gK`; `T2329b` carries over) is proposed in prove (a) l.70 and (d) l.276.
- `T2484b` (E1 as a carrier datum) is proposed in (a″) l.224 and (d) l.276.
- The constants `1 + C₆` and `C₈ A` are proof differences, not statement differences.
- Coverage is complete for U4s2a.

## 7. Observations (no RETURN)
1. Imports differ from the ticket layout: `Induction.IniTermII` instead of `Induction.IniTermI` (it is a subset), plus the merged `Evolution.CltResolvent`. No layering rule is hit. Prove (b) narrative records this.
2. Registry: only line 212 (`STIniTermIIgL`) was edited. Line 211 (`STIniTermIgL`) is left to U4s2b, whose pin it names. This is consistent with the split.
3. The check's default `T2484_KerFacts` (17 lines) is strictly weaker than target 1, so `T2484_IniTermIIOf` taken literally with the check's class is not what `stIniTermIIgL_of` proves. The ticket's binding part is the conclusion head, and the class text was fixed (with E1) at the 1a-audit. §3 compiles the pin against the fixed text.
4. The file docstring (`IniTermIIGen.lean:37`) cites the port source as commit `78f4cc14`. The last commit touching `Induction/IniTermII.lean` is `69b10990` (`git log -1 8162591d -- RBM3D/Induction/IniTermII.lean`), as prove (b) says. This is a docstring defect only.

## Verdict
Targets 1, 2, 3, 4 and their part of 10-11 (U4s2a): **PASS**. No dispatcher sign-off needed. U4s2b (targets 5-9) is not audited here; it runs on `t/T2484b`, which needs `Chain/B45Gen` in its base (H269 (2)).
