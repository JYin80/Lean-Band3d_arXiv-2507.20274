Auditor model: claude-opus-5-5

# T2130 audit (round 1) — ST2-16 + ST2-17, `stLocalAvgOfL2_holds`

Written Sun Oct  4 11:46:07 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2130-audit1`, detached at `t/T2130` = `4a77b2b` (merge base `0ce09c2`; `main` = `dab074c`).

## 1. Diff scope
```
$ git diff --name-only main...t/T2130
RBM3D/Induction/LocalAvg1.lean
RBM3D/Induction/LocalAvg2.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2130 -- RBM3D/Test/Axioms.lean   (the only hunk)
-   `RBM.Gauss.Sizes.STLocalAvgOfL2, -- closing paragraph of Step 2 (`3_5:455-465`): ST2-16, ST2-17 (T2066, DECISIONS §28)
```
Exactly the sole writable files; registry change is the one line the ticket names. No merged file (frozen signature) touched.

## 2. Statements against the pin / ticket mathematics

Pin (`Induction/Step2Defs.lean:694`, unchanged):
```
def STLocalAvgOfL2 (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        STStep1Weak sz (STflowE z) s t → STL2decayPT sz (STflowE z) s t →
          STStep2LocalPT sz (STflowE z) s t ∧ STStep2AvgPT sz (STflowE z) s t
```
Item 4 (`LocalAvg2.lean:394`): `theorem stLocalAvgOfL2_holds {d : ℕ} (hd : 3 ≤ d) : STLocalAvgOfL2 d` — the pinned name and conclusion, verbatim; extra `3 ≤ d` is the ticket's §36 form (consumer `STStep2 d := 3 ≤ d → …`, `Step2Defs.lean:599`). Proof body = `⟨stStep2LocalPT_of_L2decay …, stStep2AvgPT_of_L2decay …⟩`.

Items 2, 3 (`LocalAvg1.lean:406`, `LocalAvg2.lean:321`): binders `hd : 3 ≤ d`, `hκ hε h𝔡`, `hflow : STFlow …`, `hs hst htl`, `hweak : STStep1Weak …`, `hL2 : STL2decayPT …` = the pin's hypotheses in the pin's order; conclusions `STStep2AvgPT sz (STflowE z) s t` and `STStep2LocalPT sz (STflowE z) s t` are the merged defs (`Step2Defs.lean:275, 281`) — the general per-time (`PrecPT` over `TimeIcc s t × …`) statements, both charges/neighbour sums handled inside the proof, not by an added hypothesis.

Item 1 (`LocalAvg1.lean:343`): same hypotheses with only `0 < d`; conclusion
```
∃ ε₀ CΨ : ℝ, 0 < ε₀ ∧ 0 < CΨ ∧ ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) →
  (∀ᶠ n in atTop, W^(-d/2) ≤ stLocalPsi sz u n ∧ stLocalPsi sz u n ≤ W^(-ε₀) ∧
     sz.Bctl n (u n) ≤ stLocalPsi sz u n ^ 2 ∧ stLocalPsi sz u n ^ 2 ≤ CΨ * sz.Bctl n (u n)) ∧
  STInitialGT2 sz (STflowE z) u ε₀ (stLocalPsi sz u)
def stLocalPsi (sz : Sizes d) (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) ((sz.Bctl n (u n)) ^ (1 / 2 : ℝ))
```
Quantifier order as the ticket asks: one fixed `ε₀ > 0` before every time section `u ∈ [s,t]`, window `W^{-d/2} ≤ Ψ_u ≤ W^{-ε₀}` (paper `3_5:27`) proved eventually, `Ψ_u` = the ticket's permitted `max(W^{-d/2}, Bctl^{1/2})`, comparable to `Bctl^{1/2}` with constant `CΨ`. `ε₀ = min(1/2, d c/8)` with `c = min(2𝔡𝔠, ε)/2` of `ST_Bdata_holds` (`Step2Iterate.lean:1049`); `Ψ_u ≤ W^{-ε₀}` from `Bctl ≤ N^{-c}` for `u ≤ t ≤ lemT z` (report b.8; consistent with `localAvg1_data`, `LocalAvg1.lean:238–245`).

Paper check (`paper/tex/3_5_Loop_Hierarchy.tex:27–30, 459–462`): "(initialGT2) for a deterministic control parameter `W^{-d/2} ≤ Ψ_t ≤ W^{-ε₀}`" and "weak local law (Gtmwc) … verify the first condition in (initialGT2), then invoking lem_GbEXP, we obtain (Gt_bound_flow) and (Gt_avgbound_flow)" — matches items 1–4.

Statement verdicts: item 1 PASS, item 2 PASS, item 3 PASS, item 4 PASS.

## 3. Vacuity, hidden hypotheses, cycles
- No new structure/class; the only hypotheses are the pin's (`STFlow` is the merged flow regime of the pin itself).
- Merged dependencies used (signatures):
```
RBM3D/Green/GbEXP.lean:811:theorem stGbEXP_holds (hd : 3 ≤ d) : STGbEXP d := stGbEXP_of_v3 (gbEXPV3 hd)
RBM3D/Induction/Step2Iterate.lean:1049:theorem ST_Bdata_holds (hd : 0 < d) : STBdata d := by
RBM3D/Induction/LocalAvg1.lean:415:  refine Green.perTime_timeIcc_of_forall_seq sz.seqP sz.size hst
RBM3D/Induction/LocalAvg1.lean:422:  have hav := (Green.stGbEXP_holds hd).2.2 κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u
```
  all on `main` (T2126 `0ce09c2` and earlier). No cycle: `STLocalAvgOfL2` appears only as the conclusion; its consumer `ST_step2_of_pins` is downstream.
- External/random hypotheses `STStep1Weak`, `STL2decayPT` are other gates' outputs, kept as hypotheses as the ticket allows; limit check in the prove report (a)(ii): `Bctl(lemT) = 0.1732, 0.01986, 0.002309` at `n = 0,1,3` → 0, so both controls vanish (nonvacuous).

## 4. Compiled nonempty instances (merged flow data, `d = 3`)
Data: `sz0`, `z0`, `flow_z0 : STFlow sz0 (1/10) (1/10) (1/6) (1/10) z0` (`Induction/Defs.lean:435`), `sInst ≡ 0`, `tInst ≡ 1/16` (`Defs.lean:439–440`), `htT : ∀ n, tInst n ≤ lemT (z0 n)` (`Step2Iterate.lean:1875`); `L_n = 4(n+1)`, `W_n = (2(n+1))^5` — nondegenerate (window `[0,1/16]` open, `N ≥ 2^21`).
```
LocalAvg1.lean:453  example … : ∃ ε₀ CΨ, … STInitialGT2 sz0 (STflowE z0) (fun _ => 1/32) ε₀ (stLocalPsi sz0 (fun _ => 1/32))
                      := stInitialGT2_of_L2decay (0<3) … flow_z0 hs0 hst htT hweak hL2, section u ≡ 1/32 ∈ [0,1/16] by norm_num
LocalAvg1.lean:468  example … : STStep2AvgPT sz0 (STflowE z0) sInst tInst := stStep2AvgPT_of_L2decay (3≤3) … flow_z0 hs0 hst htT hweak hL2
LocalAvg2.lean:413  example … : STStep2LocalPT sz0 (STflowE z0) sInst tInst := stStep2LocalPT_of_L2decay (3≤3) … flow_z0 hs0 hst htT hweak hL2
LocalAvg2.lean:420  example … : STStep2LocalPT … ∧ STStep2AvgPT … := stLocalAvgOfL2_holds (3≤3) (1/10) (1/10) (1/10) … (1/6) sz0 z0 flow_z0 sInst tInst hs0 hst htT hweak hL2
LocalAvg2.lean:428  example (hNew hLWT hEMe hMart hOpt at d=3) : … STStep2Concl sz0 … := inst_step2 (ST_step2_of_pins' … (stLocalAvgOfL2_holds _))
LocalAvg2.lean:437  example {d} … : STStep2 d := fun hd3 => ST_step2_of_pins' … (stLocalAvgOfL2_holds hd3) hd3
```
Every deterministic hypothesis discharged; only `hweak`, `hL2` (and, in the last two, the other Step-2 pins) remain, as allowed. `ST_step2_of_pins'` (`Step2Iterate.lean:1779`) is `ST_step2_of_pins` with its merged pins discharged — the ticket's requested application. All four endpoints: PASS.

## 5. Build, axioms, forbidden tokens (audit worktree)
```
$ lake build RBM3D.Induction.LocalAvg1 RBM3D.Induction.LocalAvg2; echo exit=$?
exit=0
Build completed successfully (3787 jobs).
$ grep -E "LocalAvg" build.out | grep -E "error|warning"      # (no output)
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|@\[implemented_by|@\[extern' RBM3D/Induction/LocalAvg[12].lean | wc -l
       0
$ lake env lean audit.lean   # import RBM3D.Induction.LocalAvg2; example {d} (hd : 3 ≤ d) : STLocalAvgOfL2 d := stLocalAvgOfL2_holds hd; #print axioms …
'RBM.Gauss.Sizes.stLocalAvgOfL2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stInitialGT2_of_L2decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stStep2AvgPT_of_L2decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stStep2LocalPT_of_L2decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stLocalPsi' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
Registry pre-check (root imports + the two new modules + `#assert_rbm_axioms`, after building every root module):
```
$ grep '^import RBM3D' RBM3D.lean | awk '{print $2}' | xargs lake build; echo exit=$?
exit=0
Build completed successfully (3875 jobs).
$ lake env lean precheck.lean; echo exit=$?
exit=0
1:axiom audit: 3958 theorems, 1362 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
106:premises found by scanning: 73 (borrowed 1, owed 57, structural 15).
```
Name clash on `main`:
```
$ for n in …; do git grep -n "$n" main -- 'RBM3D/*.lean' 'RBM3D.lean' | wc -l; done
stLocalPsi=0 stInitialGT2_of_L2decay=0 stStep2AvgPT_of_L2decay=0 stStep2LocalPT_of_L2decay=0 stLocalAvgOfL2_holds=0 localAvg1_=0 localAvg2_=0 LocalAvg1Inst=0 LocalAvg2Inst=0
```

## 6. Paper deltas
```
$ grep -c T2130 docs/paper-deltas.md
0
```
Every Lean/paper difference is proposed in the prove report (d): `T2130a` (`Ψ_u = max(W^{-d/2}, (W^{-d}B_{u,0})^{1/2})` vs the paper's unspecified/`(W^{-d}B_{u,0})^{1/2}` control; comparable with `CΨ = cB⁻¹+1`), `T2130b` (`3 ≤ d` on items 2–4, §36), `T2130c` (one fixed existential `ε₀ = min(1/2, dc/8)`). No further difference found. Coverage complete.

## 7. Observations (no RETURN)
1. **Hub merge of `RBM3D/Test/Axioms.lean`:** `main` changed this file since the branch base (`git diff --stat 0ce09c2 main -- RBM3D/Test/Axioms.lean`: `1 file changed, 14 insertions(+), 37 deletions(-)`, T2127/T2129). Copying the branch's file would revert those changes; apply the one-line removal instead. Checked: `patch --dry-run` of `git diff main...t/T2130 -- RBM3D/Test/Axioms.lean` against `main:RBM3D/Test/Axioms.lean` → `patching file Axioms_main.lean`, exit 0; `main` still has the `STLocalAvgOfL2` line at 127.
2. `main` also changed `Propagator/Interface.lean`, `Propagator/Pins.lean` and Loop files since `0ce09c2`; this audit built on the branch base. The hub's full `lake build` at merge is the check of the new modules against `dab074c`.
3. On the branch alone the root `lake build` fails until the two `import` lines are added (report d.5): expected; the hub adds them at merge (§3 (A) 4).
4. Report (d) item 4: `STStep2LocalPT`/`STStep2AvgPT` owed lines now "carry nothing yet" in the scan — dispatcher's registry decision, not a defect of this ticket.
5. The unpinned public names `stLocalPsi`, `stInitialGT2_of_L2decay`, `stStep2AvgPT_of_L2decay`, `stStep2LocalPT_of_L2decay` are target items 1–3 (ticket gives no names); no clash.

## Verdict
| Target | Verdict |
|---|---|
| Item 1 `stInitialGT2_of_L2decay` (+ `stLocalPsi`) | PASS |
| Item 2 `stStep2AvgPT_of_L2decay` | PASS |
| Item 3 `stStep2LocalPT_of_L2decay` | PASS |
| Item 4 `stLocalAvgOfL2_holds` (pin `STLocalAvgOfL2`) | PASS |

**T2130: PASS.** No dispatcher sign-off needed (observation 1 is a merge-procedure note for the hub).
