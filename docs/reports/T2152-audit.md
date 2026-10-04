Auditor model: claude-opus-5-5

# T2152 audit (round 1) — S5-21 Evolution/CltStep (proves STCltIso)

Written: Sun Oct  4 19:13:28 UTC 2026. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2152-audit1` (detached at `t/T2152` = `80b1692`).
Targets: (1) `cltStep_loopForm` + `cltStep_loopForm_{stcltB,local,coef_le,coef_le_eventually}`; (2) `cltStep`; (3) `stCltIso_holds : STCltIso d` + registry line.

## 1. Statements

Target 3 against the pin (merged `Induction/Step5Pins.lean:426`, unchanged on the branch):
```
$ git diff main...t/T2152 -- RBM3D/Induction RBM3D/Evolution/{CltGood,CltPath,CltSwap,CltResolvent}.lean | wc -l
0
$ lake env lean stmt.lean   # import RBM3D.Evolution.CltStep; #check @stCltIso_holds; #print STCltIso; rfl-check of the unfolding
stCltIso_holds : ∀ (d : ℕ), STCltIso d
def RBM.Gauss.Sizes.STCltIso : ℕ → Prop :=
fun d => STIngR5 d (fun {d} => STReg5I) fun {d} sz E s t => sz.STCltIsoConcl E s t
exit 0
```
The endpoint's type is the pin itself (no added hypothesis, no weaker conclusion): `STIngR5 d STReg5I` with all premises
(κ, ε, 𝔡, C_d, ∃𝔠_d ≤ 1/100, STFlow, 0 ≤ s < t ≤ lemT, regime, Steps 1-4), conclusion `STCltIsoConcl` (∀ p ≥ 1, D > 0, ∀ᶠ n,
∀ σ with σ0 ≠ σ1, ∀ b : Fin (2p) → Fin 2 → Zd, window `≤ (log W)^3 ℓ_s`, ∃ isolated i at `10 (log W)^3 ℓ_s` on first labels,
`‖∫ ∏ STcltX‖ ≤ W^{-D}`). Quantifier order of the pin is kept (`𝔠_d := 1/100` chosen before 𝔠, sz, z). The proof does not
use `STReg5I`, `σ0 ≠ σ1`, nor Step 1/3/4 premises (only `STFlow`, `STStep2Concl` via `HClt`): a proof of the pin as stated,
the unused premises being harmless (paper-delta T2152b).

Target 2, `cltStep` (CltStep.lean:748; extracted in the prove report (b), re-read here): hypotheses `HClt sz κ ε 𝔠 𝔡 z s s t Cd`
(merged `CltGood.lean:64`: `3 ≤ d ∧ 0<κ ∧ 0<ε ∧ STFlow ∧ 0≤s ∧ s≤τ ∧ τ≤t ∧ t≤lemT ∧ STStep2Concl`, τ = s), a 2-label form
`F n : LocalForm d L W 2 K` with `‖coef‖ ≤ N^{C'}` eventually and `Local (w_n+1)`, `w_n = log(W)^3 ℓ_s`; conclusion: ∀ᶠ n,
∀ b, i, all windows `≤ w_n`, `10 w_n ≤ |b_i0 − b_m0|` (m ≠ i), ∀ enumeration e, ∀ j < card CoordF:
`‖∫ (X_i(hyb j) − X_i(hyb (j+1))) Γ_i(q.1) d(P⊗P)‖ ≤ N^{−D−3}`. This is the ticket's item 2 (per-step bound for the isolated
index, every coordinate), generic in F, with fixed parameters before ∀ᶠ n. The ticket's `R = 10w` is an internal parameter;
the file uses `R = 8w` after `cltFarGeomHalf` + window (`5w − w`), `θ = max(3w−2, w)`, `c = 1`; no merged statement changed.

Target 1, `cltStep_loopForm_stcltB` (CltStep.lean:1195): for `|b0−b1|_∞ ≤ w_n`,
`STcltB sz n E s σ b ω = cltEvalAt (cltStep_loopForm sz n s σ) E s (slice n ω) b − scale·STKloop` — the equality of
`STcltB` with the 2-label form up to the deterministic 𝒦 constant, as the ticket asks; `cltStep_loopForm_local`:
`Local (w_n + 1)` for every n, s, σ; `cltStep_loopForm_coef_le`: `‖coef‖ ≤ scale`; `..._eventually`: `≤ N^2` under WO, N→∞
(ticket asked `≤ N^{C'}`; C' = 2). The form vanishes outside the window, which is exactly the pin's window premise.

Verdict on statements: all three PASS.

## 2. Vacuity, hidden hypotheses, cycles
```
$ grep -rn "STCltIso" RBM3D/Evolution/ | grep -v CltStep.lean     # only docstrings mention it; no merged dep assumes it
RBM3D/Evolution/CltSwap.lean:28:This is the first brick of the proof of `STCltIso` ...
RBM3D/Evolution/CltResolvent.lean:18:... (`STCltIsoConcl`) ...
RBM3D/Evolution/FarEntry.lean:30: / :671:  (docstrings)
```
- `HClt` is a conjunction `def` of pin premises (listed above), not a structure carrying extra content; in `stCltIso_holds` it is
  built from the pin's premises: `⟨hd, hκ, hε, hflow, hs0, fun n => le_rfl, fun n => (hst n).le, htl, hS2⟩`.
- `hcoef`, `hloc` of `cltStep` are discharged in `stCltIso_holds` by `cltStep_loopForm_coef_le_eventually` (from `STFlow`'s
  `WO`, `SizeTendsto` via `v3_premises_of_stFlow`) and `cltStep_loopForm_local`. No new `Prop`-valued definition is introduced.
- Dependencies are merged: CltGood (T2149), CltPath/CltResolvent (T2144), CltSwap (T2140), FarEntry (T2141), Step5Pins (S5-01).
No hidden hypothesis, no cycle. PASS.

## 3. Compiled nonempty instances (same file, section 8; all compile in the build below)
```
$ grep -n "^example" RBM3D/Evolution/CltStep.lean
1509:example : InstIng5Concl (fun sz E s t => STCltIsoConcl sz E s t) szCL zCL sCL tCL 1 :=   -- inst_cltIso (stCltIso_holds 3) 1 one_pos
1512:example : ∀ n, ∃ b : Fin (2 * 1) → (Fin 2 → Zd 3 (szCL.L n)), ... 0 < zdistInf ... ∧ (∃ i, ...)  -- pin premises satisfiable
1527:example : STCltIso 3 := stCltIso_holds 3
1533:example (n : ℕ) (E : ℝ) (ω : szCL.SeqΩ) : ∃ b, 0 < zdistInf .. (b 0 - b 1) ∧ STcltB .. = cltEvalAt .. − scale·STKloop ∧ Local ∧ coef ≤ scale
1557:example (hStep2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) := cltStep szCL (1/10) (1/10) (1/6) (1/10) zCL sCL tCL 1 (cltGood_hclt_szCL hStep2) 2 2 ...
1567:example (hStep2 : ...) := (cltStep ...).mono fun n hn => hn (cltStep_szCL_witness n).choose 0 ...   -- specialised at the witness
```
- Target 3: `inst_cltIso` (merged, Step5Pins:967) discharges every deterministic premise at `szCL` (d = 3, `L_n = 2(n+24)^5`,
  `W_n = 2^{n+24}`, λ = 1, `s ≡ 0`, `t = 1 − L^{-2}`, flow `zCL`, regime, con_st_ind); only stochastic Step 1-4 pins remain as
  premises inside `InstIng5Concl` (other gates). Premises of `STCltIsoConcl` satisfiable at every n with a **positive** window
  `m² > 0` (`cltStep_szCL_witness`, `m = n+24`; isolation `10(log W)^3 ≤ 10 m³ ≤ m⁵`), i.e. not the window-0 merged witness.
- Target 2: all deterministic hypotheses discharged (`cltGood_hclt_szCL`, `cltStep_szCL_coef`, `cltStep_loopForm_local`, p = 1,
  D = 1); only `STStep2Concl` (another gate's pin) stays a hypothesis; specialised at the positive-window isolated labels.
- Target 1: at `szCL`, σ = (+,−), the positive-window label pair.
Nondegenerate (L_n → ∞, N > 0, nonempty labels, window > 0, no False premise). PASS.

## 4. Build, axioms, hygiene, diff
```
$ lake build RBM3D.Evolution.CltStep      (audit worktree; CltStep.olean mtime 2026-10-04 19:10 UTC)
Build completed successfully (3809 jobs).
exit 0
$ grep -c "CltStep.lean.*error" build.out ; grep "CltStep.lean.*warning" build.out | wc -l
0
0
$ grep "CltStep.lean.*depends on axioms" build.out | sed 's/.*info: //'
'RBM.Evol.cltStep_pairForm_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltStep_loopForm_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltStep_loopForm_local' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltStep_loopForm_coef_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltStep_loopForm_coef_le_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltStep_loopForm_stcltB' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltStep_scale_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Evol.cltStep' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stCltIso_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.cltStep_zdistInf_yCL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.cltStep_szCL_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.cltStep_szCL_coef' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -n -E "\bsorry\b|\badmit\b|native_decide|^\s*axiom " RBM3D/Evolution/CltStep.lean | wc -l
0
$ git diff --name-only main...t/T2152
RBM3D/Evolution/CltStep.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2152 -- RBM3D/Test/Axioms.lean | grep '^[-+]' | cut -c1-110
--- a/RBM3D/Test/Axioms.lean
+++ b/RBM3D/Test/Axioms.lean
-   `RBM.Gauss.Sizes.STCltIso, -- `(eq:bound_isolated)`; proved internally (DECISIONS §40); S5-01 (T2138, DECI
```
Registry pre-check (scratch file = the 195 `import` lines of the branch's `RBM3D.lean` + `import RBM3D.Evolution.CltStep` +
`#assert_rbm_axioms`; after `lake build RBM3D.Test.Axioms` and the 195 modules):
```
$ lake env lean precheck.lean; echo exit $?
exit 0
axiom audit: 4659 theorems, 1657 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 86 (borrowed 0, owed 66, structural 20).
$ grep -c STCltIso precheck.out ; grep -ci error precheck.out
0
0
```
Name clashes on current `main` (88600b1): `git grep -E "(def|theorem|lemma|abbrev) <n>( |$)" main -- RBM3D` gives 0 for each of
cltStep, stCltIso_holds, cltStep_{Xo,Gamma,win,pairForm,scale,c2,loopForm,yCL,szCL_witness,szCL_coef}. Unpinned helpers are
`private` or prefixed `cltStep_` (§3 (E)). PASS.

## 5. Paper deltas
Lean/paper differences and their coverage (prove report (d)):
- proof route (i.i.d. copy + coordinate telescope) and log-scale constants ρ = w+1, R = 8w, θ = 3w−2 not in the paper: **T2152a**;
- the theorem holds without `STReg5I` and for all σ (pin has σ0 ≠ σ1): **T2152b**;
- `𝗕_b` encoded as a 2-label local form with coefficient `scale·W^{-2d}`, zero outside the window: **T2152c**.
No uncovered statement difference found. PASS.

## Observations (no verdict impact)
- O1 (hub, merge): `main` has removed two other registry lines from `RBM3D/Test/Axioms.lean` since the branch base `4f4612b`
  (`STNewKLKL` by T2150, `STExpInv` by T2155). Bring in only this ticket's one-line deletion of `STCltIso` (e.g. apply the
  branch diff), not the branch's whole file, or those two lines come back.
- O2 (hub, merge): the registry deletion needs `import RBM3D.Evolution.CltStep` in `RBM3D.lean` in the same merge (pre-check above
  passes with it; prove report shows the root build fails without it).
- O3: section (a) of the prove report states `C' = 6`, `a = 14`; corrected in (a′) to `C' = 2`, `a = 10`, consistent with the Lean.

## Verdict
- Target 1 (local form of `STcltB`): PASS.
- Target 2 (`cltStep`): PASS.
- Target 3 (`stCltIso_holds : STCltIso d`, registry line deleted): PASS.
**T2152: PASS.** No dispatcher sign-off needed.
