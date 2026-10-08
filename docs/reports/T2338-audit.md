Auditor model: claude-opus-5-5

# T2338 (ST-D6, report-only design) — audit round 1

Written Thu Oct  8 17:06:36 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2338-audit1`, detached at `t/T2338` = `854aa29` (merge-base with `main`: `3f750b6`).
Targets (ticket): T1 = `docs/reports/T2338-design.md` answering Q1-Q6 with line-cited evidence; T2 = the probe `RBM3D/Probe/T2338Pins.lean` (branch only, compiles); the candidate pin of the check file section 2, `∀ d, STMainInd d → UNMLOut d`.

## 1. Build, axioms, hygiene (audit worktree)
`lake build RBM3D.Probe.T2338Pins` (log filtered to the probe and the tail):
```
ℹ [4038/4038] Built RBM3D.Probe.T2338Pins (6.1s)
info: RBM3D/Probe/T2338Pins.lean:31:0: STMainInd : ℕ → Prop
info: RBM3D/Probe/T2338Pins.lean:33:0: STLocalMax_of_STLocalEntry : ∀ (d : ℕ) (sz : Sizes d) (E τ : ℕ → ℝ), sz.STLocalEntry E τ → sz.STLocalMax E τ
info: RBM3D/Probe/T2338Pins.lean:36:0: Endpoints.fixed_of_ML : Endpoints.MAFixed
info: RBM3D/Probe/T2338Pins.lean:396:0: 'RBM.Probe.T2338.stMLOutG_of_mainIndG' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Probe/T2338Pins.lean:397:0: 'RBM.Probe.T2338.stBase_band' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Probe/T2338Pins.lean:398:0: 'RBM.Probe.T2338.unMLOut_of_mainInd' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Probe/T2338Pins.lean:399:0: 'RBM.Probe.T2338.unMLOutBA_of_pins' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (4038 jobs).
lines starting with "error": 0
```
`grep -c -E '\bsorry\b|\badmit\b|native_decide|^axiom' RBM3D/Probe/T2338Pins.lean` → `0`.
`git diff --stat main...HEAD`:
```
 RBM3D/Probe/T2338Pins.lean | 399 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 399 insertions(+)
```
Only a sole writable file is touched; no merged file changed. Sizes: probe 399 ≤ 400, design 330 ≤ 400, prove report 286 ≤ 300. The design report lives in the main worktree (`docs/reports/`), as reports do; report-only merge.

## 2. Statements against the merged pins (the probe compiles them by `Iff.rfl`)
Merged `UNMLOut` (`Universality/Pins.lean:432`) and `STMainInd` (`Induction/Defs.lean:294`), verbatim from the worktree:
```
def UNMLOut (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 𝔠 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ),
    STFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
      STLK sz (STflowE z) t ∧ STLmax sz (STflowE z) t ∧ STDecay sz (STflowE z) t ∧
        STExp2 sz (STflowE z) t ∧ STLocalEntry sz (STflowE z) t
def STMainInd (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → (∀ n, s n < t n) → ...
```
- Probe `STMLOutG` (69-76) has the same binder order `κ ε 𝔡 𝔠 → sz z → Flow → t` and the same five conclusions; `unMLOut_iff` (357-358) is `Iff.rfl`, and `unMLOutBA_of_pins` (365-369) closes `UNMLOutBA` (`BA/UNPins.lean:110`) by unification: both compile, so the generic statement is literally the two consumer pins, not a variant.
- `stMLOutG_of_mainIndG` takes exactly `STMainIndG` (merged, `BA/FlowPins.lean:565`), `STHorizonG`, `STBaseG`; the band instances of the last two are proved (`stHorizon_band`, `stBase_band`). `𝔠_d` is obtained from `hmain` before `𝔠, sz, z`, and `K` from `exists_nat_ge` after `𝔠` and before the sequence `t` (probe 268-271): the chain length does not depend on `n` or `t`. Every `t` with `0 ≤ t_n ≤ T0` is covered (Q3), with the class `t_n = 0` handled by `StochDomAt.of_subset_union` (`Defs/StochDomAt.lean:355`).
- Q2 closure: the merged bridge `STLocalMax_of_STLocalEntry` exists (#check above, `MainIndRegimes.lean:244`); the generic twin (244-254) compiles.

## 3. Candidate pin of the check file; vacuity of the extra hypothesis
`unMLOut_of_mainInd` carries one hypothesis beyond the pin, `STLoopZeroId d` (probe 340-342). Its text matches the merged private `azumaProxy_loopFine_sub_STKloop` (`Induction/AzumaProxyN.lean:597-601`, section variables `sz n`). Independent check (scratch file `T2338/zeroid.lean`, run with `lake env lean` in the audit worktree):
```
import RBM3D.Probe.T2338Pins
open RBM RBM.Ind
open private azumaProxy_loopFine_sub_STKloop from RBM3D.Induction.AzumaProxyN
example (d : ℕ) : RBM.Probe.T2338.STLoopZeroId d := fun sz n _ hE _ hm σ a =>
  azumaProxy_loopFine_sub_STKloop sz n hE hm σ a
theorem auditT2338_target : ∀ d : ℕ, RBM.Gauss.Sizes.STMainInd d → RBM.Univ.UNMLOut d := fun _ hmain =>
  RBM.Probe.T2338.unMLOut_of_mainInd (fun sz n _ hE _ hm σ a => azumaProxy_loopFine_sub_STKloop sz n hE hm σ a) hmain
#print axioms auditT2338_target
--- output (one unused-variable warning omitted) ---
'auditT2338_target' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
So `STLoopZeroId` is a true, non-vacuous statement (proved in the repository), and the check-file candidate `∀ d, STMainInd d → UNMLOut d` holds **exactly**, with no extra hypothesis. No hidden hypothesis in a structure field: `STHorizonG`/`STBaseG` are explicit `Prop` premises with proved band instances; the only owed input is the merged pin `STMainInd` (no cycle: the probe proves nothing upstream of it).

## 4. Compiled nonempty instances (probe 373-392)
- `example (hpriv : STLoopZeroId 3) (hmain : STMainInd 3) : sz0.STLK (STflowE z0) (fun n => lemT (z0 n) / 2)` applies `unMLOut_of_mainInd` at `d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, merged `sz0`, `z0`, `flow_z0`, `t = lemT z0/2` (strictly inside `(0, lemT)`, both bounds discharged by `lemT_pos (z0_im_pos n)`). `STMainInd 3` is an owed pin (allowed); `STLoopZeroId 3` is deterministic but true (section 3), so the instance is nondegenerate.
- `stChainSteps` at `sz0`, `z0`, `K = 6000`, last step `k = 5999`, every hypothesis discharged (`hbw hWO hsz hr` from `flow_z0` via `stHorizon_band`).
- `STMainInd d` from `LWterm d`, `LWtermExp d`, `STDuhamelII d` (R4a): compiles; on main `STDuhamelII` is proved (`stDuhamelII_holds`, design B13).

## 5. Citations (ticket: "the audit checks each cited line")
Independent echo of every `path.lean:line` in design sections 0-9 (script `T2338/cites.py`; RBM3D at the worktree = base for non-probe files, RBM2D via `git show c9a24cf:`), excerpt; full output 104 lines, all on the cited declaration:
```
BA/FlowPins.lean:565 «def STMainIndG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.Seq»
Defs/StochDomAt.lean:355 «theorem of_subset_union (hsize : Tendsto size atTop atTop)»
Graph/LWExpTerm3.lean:1675 «theorem lwExpTerm3_Gt_zero {E : ℝ} (hE : |E| < 2) (ω : sz.Se»
Induction/AzumaProxyN.lean:597 «private theorem azumaProxy_loopFine_sub_STKloop {E : ℝ} (hE »
Induction/Defs.lean:294 «def STMainInd (d : ℕ) : Prop :=»
Induction/MainIndRegimes.lean:244 «theorem STLocalMax_of_STLocalEntry (d : ℕ) (sz : Sizes d) (E»
Induction/ScaleFacts.lean:193 «theorem scaleFacts_R1 (𝔠 𝔡 τ : ℝ) (t : ℕ → ℝ) (h𝔡 : 0 < 𝔡)»
Induction/Step2Iterate.lean:1014 «theorem ST_one_sub_lemT {z : ℂ} (hz : 0 < z.im) : z.im / (1 »
Induction/Step4.lean:209 «theorem ST_mainInd_of_pins' (d : ℕ) (h2 : STStep2 d) (h3III »
Loop/KLFinal.lean:302 «theorem stKbound_of_flow (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 »
Main/FixedZ.lean:121 «obtain ⟨hLK, -, -, -, hLoc⟩ := hML d hd κ ε 𝔡 𝔠 hκ hε h𝔡 sz »
Main/FixedZ.lean:444 «obtain ⟨hLK, -, hDec, hExp, -⟩ := hML d hd κ ε 𝔡 𝔠 hκ hε h𝔡 »
Main/FixedZ.lean:538 «theorem fixed_of_ML : MAFixed := fun hML => ⟨locSCFixed_of_M»
RBM2D/Induction/Defs.lean:318 «def chainTime (t : ℕ → ℝ) (n₀ k : ℕ) (n : ℕ) : ℝ :=»
RBM2D/Universality/Pins.lean:238 «def P7Out : Prop :=»
Test/Axioms.lean:108 «`RBM.Gauss.Sizes.STMainInd,      -- `lem:main_ind`: end of t»
Universality/Pins.lean:432 «def UNMLOut (d : ℕ) : Prop :=»
Universality/Pins.lean:793 «def UNOURow : Prop := (∀ d : ℕ, UNMLOut d) → UNLocAvgBand → »
-- 94 distinct path:line citations, 103 lines echoed, missing files: 0
```
Paper lines (`sed -n <l>p paper/tex/1_2_Intro_model_result.tex | cut -c1-70`):
```
1_2:1240 «Before concluding this section, we now outline the proofs of \Cref{ML:»
1_2:1256 «\begin{theorem}\label{lem:main_ind} »
1_2:1277 « \|G_{s}-M\|_{\max} \prec (W^{-d}B_{s,0})^{1/2}.»
1_2:1296 «\begin{equation}\label{con_st_ind}»
1_2:1309 «\begin{proof}[\bf Proof of \Cref{ML:GLoop,ML:GLoop_expec,ML:GtLocal}]»
1_2:1400 «We remark that the estimates established in each step hold uniformly i»
```
The 1_2:1310 text ("induction from t=0 up to t=1-λ² ... t_1:=(1-λ²)∨1/2") matches the design's two-phase description (section 1, T2338a).

## 6. Q1-Q6 coverage
| Q | answered where | audit check |
|---|---|---|
| Q1 base case | design §2 table (merged / trivial / owed per predicate) | generic zero lemmas and `stBase_band` compile; the one "owed" item is proved privately (section 3) |
| Q2 closure | §3 | merged bridge exists; generic twin compiles |
| Q3 chain | §4 | fixed `K` before `t`; run to each `t_n`; class `t_n = 0` by `of_subset_union`; compiles |
| Q4 shape | §5 | candidate holds exactly (section 3); MA uses only the five conclusions (FixedZ:121, :444) |
| Q5 route G | §6 | `UNMLOutBA` closes from the generic theorem by unification (compiles) |
| Q6 rows | §7 | R1-R4 with sizes, roles, dependencies, registry classes (for sign-off); `stMainInd_holds` owned by R4 |

## 7. Paper deltas
Candidates `T2338a` (uniform grid vs two phases), `T2338b` (`lem:main_ind` excludes `t = 0`; base case supplies it), `T2338c` ("uniformly in t" per sequence; no `N^{-C}`-net), `T2338d` (base case uses `ML:Kbound` for `STLmax`) are proposed in design §8 and prove report (d); `grep -n T2338 docs/paper-deltas.md` → no lines (dispatcher appends). Every Lean/paper difference of the probe's statements is covered; `STLoopZeroId`, `STHorizonG` (`ε/2`) are Lean-internal, not paper deltas.

## 8. Observations (no RETURN)
- O1. Section 3 shows a third route for R1 besides "port 120 lines" and "drop `private`": `open private azumaProxy_loopFine_sub_STKloop from RBM3D.Induction.AzumaProxyN` in the R1 file (0 edits to merged files, 0 ported lines). Whether `open private` is acceptable in library code is a dispatcher choice (design open question 1).
- O2. The design's statement that the identity is "owed" (Q1 table) is correct for public API only; mathematically it is proved in the repository.
- O3. Registry classes of the new pins (design §7) and the fate of `Test/Axioms.lean:102-107` are proposals that need dispatcher decisions when the rows are written; they do not affect this report-only ticket.

## Verdict
- T1 design report: **PASS** (Q1-Q6 answered; every cited line checked; no merged pin contradicts the chain).
- T2 probe: **PASS** (builds, axioms standard, no `sorry`; branch only, never merged).
- Candidate `∀ d, STMainInd d → UNMLOut d`: confirmed, and compiled without extra hypothesis (section 3).
Overall: **PASS**. No dispatcher sign-off is needed for the merge; O1/O3 are inputs to the row tickets.
