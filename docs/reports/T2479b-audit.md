Auditor model: claude-opus-5-5
# T2479b audit (X1b-2 of T2479: targets 5-9, `RBM3D/Evolution/CltFarG.lean`), round 1
Date: Tue Oct 13 00:53:16 UTC 2026 (`date -u`). Branch `t/T2479b` = 9bedb306; `main` = ddfbcae3. Audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2479b-audit1` (detached at 9bedb306). Scratch: `scratchpad/T2479b/` (`audit_check.lean`, `stmts.txt`, `build.log`).

## 1. Diff scope, imports, size
```
$ git diff --stat main...t/T2479b
 RBM3D.lean                   |    1 +
 RBM3D/Evolution/CltFarG.lean | 1070 ++++++++++++++++++++++++++++++++++++++++++
 2 files changed, 1071 insertions(+)
$ git diff main...t/T2479b -- RBM3D.lean | grep ^[+-]
--- a/RBM3D.lean
+++ b/RBM3D.lean
+import RBM3D.Evolution.CltFarG
$ git diff main...t/T2479b -- <CltMoments1 CltMoments2 MeanFar CltFar CltMoments2G MeanFarG> RBM3D/Chain RBM3D/Induction RBM3D/BA RBM3D/Test | wc -l
       0
$ grep -n ^import CltFarG.lean
6:import RBM3D.Evolution.CltFar
7:import RBM3D.Evolution.CltMoments2G
8:import RBM3D.Evolution.MeanFarG
$ wc -l CltFarG.lean
    1070
$ git merge-base --is-ancestor 82deb62b t/T2479b; echo $?
0
```
Only sole writable files touched (`CltFarG.lean`, `RBM3D.lean` import line). Imports are the Layout's. 1070 < 1800, so the reserve `CltFarG2` is not
needed. No band, chain, induction, BA or registry file is edited, so the frozen signatures and G1 (the 97 band names) are unchanged by construction.
X1b-1 (82deb62b) is an ancestor.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Evolution.CltFarG     (grep -c ^error: 0; CltFarG lines verbatim)
ℹ [3825/3825] Built RBM3D.Evolution.CltFarG (10s)
info: RBM3D/Evolution/CltFarG.lean:1060:0: 'RBM.BA.cltFar_domg' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltFarG.lean:1061:0: 'RBM.BA.cltFar_offg' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltFarG.lean:1062:0: 'RBM.BA.cltFar_flucg' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltFarG.lean:1063:0: 'RBM.BA.stCltFargL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltFarG.lean:1064:0: 'RBM.BA.bandFM_STThPropsg' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltFarG.lean:1065:0: 'RBM.BA.bandFM_STKpropsg' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltFarG.lean:1066:0: 'RBM.BA.stCltFar_of_gL' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3825 jobs).
exit=0
$ grep -nE "sorry|admit|native_decide|^\s*axiom " CltFarG.lean | wc -l
       0
$ lake env lean docs/tickets/checks/T2479-check.lean   (in the audit worktree)
check_exit=0 errors=0
```
The full `lake build` (registry scan, `#assert_rbm_axioms`) is the hub's at merge.

## 3. Statements against the pins (auditor's check `audit_check.lean`)
The file copies by script the `def T2479_FarPin/ThPropsBand/KPropsBand/BandFar` text from `docs/tickets/checks/T2479-check.lean`, imports
`RBM3D.Evolution.CltFarG`, and adds:
```
example : T2479_FarPin := stCltFargL_holds
example : T2479_ThPropsBand := @bandFM_STThPropsg
example : T2479_KPropsBand := @bandFM_STKpropsg
example : T2479_BandFar := stCltFar_of_gL
-- typed example of the pin, text unfolded from Chain/CltGen.lean:167-172
example : ∀ d : ℕ, ∀ (κ δ 𝔠 𝔡 Cd : ℝ) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (g' E : ℕ → ℝ)
    (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (s t : ℕ → ℝ),
    HCltOf C μ H₀ g' E κ δ 𝔠 𝔡 Cd s t → STReg5I sz s t → STThPropsg C → STKpropsg C s → STExpInvgL C μ →
      STCltFarConclgL C μ s t := fun d => stCltFargL_holds d
example : ∀ d : ℕ, STCltFargL d → STCltFar d := stCltFar_of_gL
example : ∀ d : ℕ, STCltFar d := fun d => stCltFar_of_gL d (stCltFargL_holds d)
-- d = 3 band instance of target 6 together with nonemptiness of its index set (Step-2 pins as the only hypotheses)
example (hLoc : STLocalEntryUgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL)
    (hDec : STGdecayWgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL 1) :
    STCltFarConclgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL ∧ ∀ n, Nonempty {p : … // <window of STCltFarConclgL>} := …
$ lake env lean scratchpad/T2479b/audit_check.lean
'RBM.BA.stCltFargL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
… (same three axioms for the other six)
exit=0
```
- **Target 6** `stCltFargL_holds (d : ℕ) : STCltFargL d`: the merged pin exactly, for every `d`. No premise added. `Chain/CltGen` is untouched (§1).
- **Target 7a/7b**: these elaborate against `T2479_ThPropsBand` / `T2479_KPropsBand` via `@`. The premise lists equal the check's proposals and the conclusions are binding.
- **Target 8** `stCltFar_of_gL (d) (hF : STCltFargL d) : STCltFar d` = `T2479_BandFar` up to the name.
- **Target 5** (no pin; the ticket's mathematics is band `CltFar.DomStmt/OffStmt/FlucStmt`, `CltFar.lean:73-104`). The statements (`stmts.txt`, prove report b4)
  are the band ones with these replacements: `STGdecayWgL` for `STGdecayW`, `κ ≤ Im (C.m n)` for `|E| ≤ 2-κ`, `μ` and `CltRepg` for `seqP`,
  `STCltIsoConclgL` for `STCltIsoConcl`, plus the pin premises `STThPropsg`, `STKpropsg`. Quantifier order (fixed parameters, then `∀ᶠ n`, then `σ`, `a`), the
  exponents `N^τ`, `N^{-D₁}`, `W^{-D}`, `N^{-D'}`, `A^{-6/5}`, `|a₀-a₁|^{d-2}` and the prefactor `(1-s)²/(λ⁴(λ²W^d)^{6/5})` match the band text. One
  difference: `cltFar_offg` is for mixed `σ 0 ≠ σ 1` only (band: every `σ`). This is the range of the generic pins and the index set of `STCltFarConclgL`, and
  the report covers it in (d) / `T2479c`. Target 5 is an intermediate with no outside reader.

## 4. Hypotheses, vacuity, cycles
- The premises of targets 5, 6 and 8 are merged named Props (`HCltOf`, `STReg5I`, `STThPropsg`, `STKpropsg`, `STExpInvgL`, `STGdecayWgL`, `CltRepg`,
  `STCltIsoConclgL`) or explicit inequalities. No new structure or `def` carries a hypothesis. Private `cltFarG_H` is a `Prop` abbreviation used inside
  proofs only.
- X1-C4 / TN-C4 / UBA-C1 / U-C4 grep over the whole file:
```
$ grep -nE "(def|abbrev|structure) (STCltFargL|HCltOf|STThPropsg|STKpropsg|STExpInvgL|STCltFarConclgL|STfFarg|STcltBg|STcltXg|STGijDecgL)|STGridRepNgL|gK|withLam|lam0|BAflowLam0|seqHflowBA|Ring.inverse|Matrix.of|Theta d|^import RBM3D.BA|IniTerm" CltFarG.lean
490:  have : IsProbabilityMeasure μ := by rw [hrep.1]; exact Sizes.isProbabilityMeasure_seqP (sz.withLam g')
662:  have : IsProbabilityMeasure μ := by rw [hrep.1]; exact Sizes.isProbabilityMeasure_seqP (sz.withLam g')
811:  have : IsProbabilityMeasure μ := by rw [hrep.1]; exact Sizes.isProbabilityMeasure_seqP (sz.withLam g')
910:`gK = sz.lam` (no comparison text).  The proof is the private producer of `MeanFarG` (`open private`). -/
```
  The hits are proof lines that read merged `CltRepg`'s law field, and one docstring. None is in a statement.
- X1-C1 / UBA-C1 grep over the statement text of the 7 public theorems (`stmts.txt`, extracted by script up to `:=`):
```
$ grep -noE "mE|zt E|…|seqP|seqHflow" stmts.txt | sort | uniq -c        (line = theorem)
   1 5: 2 - κ          (5 = bandFM_STThPropsg, target 7a)
   1 6: 2 - κ          (6 = bandFM_STKpropsg, target 7b)
$ grep -cE "gK|withLam|lam0|BAflowLam0|seqHflowBA" stmts.txt
0
```
  X1-C1 hits only in target 7 (band side, allowed). The generic targets 5, 6 and 8 are clean. UBA-C1 is empty.
- No cycle: the imports are `CltFar`, `CltMoments2G`, `MeanFarG` (merged), with no `BA/*` or `IniTerm*`. `stCltFargL_holds` uses merged `stCltIsogL_holds`
  and `meanFar_eventuallyg` (X1b-1). The band producers are `meanFarG_chk_Th/_K` (merged X1b-1 privates, `open private`). No new external hypothesis.
- Name clash:
```
$ git grep -nE "^(private )?(theorem|lemma|def|abbrev) (cltFar_domg|cltFar_offg|cltFar_flucg|stCltFargL_holds|bandFM_STThPropsg|bandFM_STKpropsg|stCltFar_of_gL|cltFarG_)" main -- RBM3D | wc -l
       0
$ grep -nE "^private (theorem|def|lemma)" CltFarG.lean | grep -vc " cltFarG_"
0
```

## 5. Compiled nonempty instances (`CltFarG.lean:952-1056`, compiled in §2)
Data: `d = 3`, `szCL` (`L_n = 2(n+24)^5`, `W_n = 2^{n+24}`, `λ ≡ 1`), `bandFM szCL (STflowE zCL)`, `seqP szCL`, `sCL ≡ 0`, `1 - tCL = L^{-2}`, `κ = 1/2`,
`𝔠 = 1/6`, `𝔡 = 1/10`, `Cd = 1`. This data is nondegenerate.
| target | example line | open hypotheses | deterministic premises discharged by |
|---|---|---|---|
| 5a `cltFar_domg` | 986 | `STGdecayWgL` | `szCL_admissible`, `cltFarG_chk_s1`, `szCL_hst`, `szCL_reg5I`; specialised to `σ=(+,-)`, `β=(0,0)` |
| 5b `cltFar_offg` | 1006 | `STGdecayWgL` | `meanFarG_chk_m` (κ ≤ Im m), `cltRepg_band`, `szCL_reg5I`, targets 7a/7b at szCL |
| 5c `cltFar_flucg` | 1019 | `STLocalEntryUgL`, `STGdecayWgL` | as 5b, plus `stCltIsogL_holds` on `cltGood_hCltOf_szCL`; `σ=(+,-)`, `a=(x_n,0)` |
| 6 `stCltFargL_holds` | 1040 | `STLocalEntryUgL`, `STGdecayWgL` | `cltGood_hCltOf_szCL`, `szCL_reg5I`, 7a, 7b, `stExpInvgL_band`; index set nonempty (1049; auditor's conjoined example §3) |
| 7a, 7b | 977, 980 | none | `szCL_WO`, `meanFarG_chk_E` (`|E| ≤ 3/2`), `meanFarG_chk_t1`, `szCL_reg5I` |
| 8 `stCltFar_of_gL` | 1052 | none | `example : STCltFar 3 := stCltFar_of_gL 3 (stCltFargL_holds 3)` (closed) |
`cltGood_hCltOf_szCL` (`CltGood.lean:1002`) takes exactly `hLoc`, `hDec`. These are Step-2 pins of another gate, which the ticket allows to stay as hypotheses. No `N = 0`,
no empty index and no `False` premise.

## 6. Paper deltas
`docs/paper-deltas.md` has no T2479 entry yet. The prove report (d) proposes `T2479c`: `c_Θ = max(C₅(1+2^{d-1}), c₁)` and `κ' = κ` in the generic far
steps. It also records the mixed-`σ` restriction of `cltFar_offg` as an observation. The pin statement `STCltFargL` itself is X1a's (merged), so its paper deltas are
X1a's. I found no other Lean/paper statement difference in targets 5-9. Coverage is adequate.

## 7. Observations (no RETURN)
- O1. The candidate tag `T2479c` is in this report while X1b-1 used `T2479b`. Tags are distinct, so the dispatcher numbers them.
- O2. `CltFarG` depends on the X1b-1 privates `meanFarG_chk_*` and `meanFarG_B*` via `open private` (prove report O1). A rename in `MeanFarG` would break it.
- O3. The docstring at `:910` mentions `gK = sz.lam`. It is a comment, not statement text.
- O4. The registry comments `Test/Axioms.lean:222-223` do not list the new users of `STThPropsg`/`STKpropsg` (prove report O2). The comment is not wrong.

## Verdict
| target | verdict |
|---|---|
| 5 `cltFar_domg`, `cltFar_offg`, `cltFar_flucg` | PASS |
| 6 `stCltFargL_holds` | PASS |
| 7 `bandFM_STThPropsg`, `bandFM_STKpropsg` | PASS |
| 8 `stCltFar_of_gL` | PASS |
| 9 instances | PASS |
Overall: **PASS**. No dispatcher sign-off needed.
