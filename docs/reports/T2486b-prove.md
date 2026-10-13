Prover model: claude-sonnet-5-5
## (a) Math preflight: see `docs/reports/T2486-prove.md` section (a) (the pre-signed split's 1a; `B45BA` = its items 6-8, rows 12, 13, 16). No (a′): no correction needed.
## (b) Script output: U2-BA part (b), `RBM3D/BA/B45BA.lean` on `t/T2486b`
Branch `t/T2486b` started at `t/T2486` 19c7f4c7; `main` 4e78c3da merged in as 008b37f6 (06:11:02 UTC; the one `RBM3D.lean` conflict was resolved by taking `main`'s file, which already holds the two part-(a) import lines); then 3b47302c (06:21:48 UTC): `RBM3D/BA/B45BA.lean` (new, 399 lines) and one import line in `RBM3D.lean`. Scratch: `scratchpad/T2486b/`.
### (0) Name-level tables of the 1b start (written before any Lean)
Targets here = items 6-8 of the ticket's list: 6 `baZeroModeGen_kerSums`, `baB45Gen_facts`; 7 `baWardTypePgL_of`, `baB45gL_of`; 8 `BAWardTypePPin`, `BAB45Pin` and `baWardTypePPin_holds`, `baB45Pin_holds`.
| field of `B45Gen_Facts` (`Chain/B45Gen.lean:61`) | BA source (file:line) |
|---|---|
| `ZeroModeGen_WardCls` | `baZeroModeGen_wardCls` (`BA/SEforLnBA.lean:66`, merged 7be99aae) |
| `DecayGen_WardPair` | `DecayGenTw_baWardPair` (`Chain/DecayGenTw.lean:44`) |
| `Im m ≤ 1` | `EMn2BA_mF_data` (`BA/EMn2BA.lean:125`, `.2`) |
| `ZeroModeGen_KerSums` (`Chain/ZeroModeGen.lean:54`), four charge pairs | `Step2Kern_Mss_BA` (`Chain/Step2Kern.lean:73`), `BAMB_shift` (`BA/Ward.lean:53`), `BAMB_symm` (`BA/Ward.lean:83`) |
| row sums of `‖thetaKer‖` | `Step2Kern_thetaKer_BA` (`Step2Kern.lean:90`), `BATheta_resolvent` (`BA/KBase.lean:330`), `BAMss_norm_eq_BAK` (`BA/KKernel.lean:102`), `BAK_row_sum` (`KKernel.lean:124`), `Matrix.linfty_opNorm_mul` (Mathlib `Analysis/Matrix/Normed.lean:356`), `sum_norm_row_le` (`Kernel/Evolution.lean:78`) |
| column sums of `thetaKer` | `QopAlgebra_col_sum_thetaKerg` (`ZeroModeGen.lean:419`), `BATheta_isUnit` (`KBase.lean:324`) |
| `BAReal` at every `n` | `BAflow_real` (`BA/GreenSchur.lean:59`) |
| `STKcalDecaygL` (pins, `3 ≤ d`) | `baKcalDecay_holds` (`BA/KDecayBA.lean:692`, merged) |
| `Step5CasesGen_FlowFacts` | `baStep5CasesGen_flowFacts` (`BA/SEforLnBA.lean:152`, merged) |
| generic theorems | `stWardTypePgL_of` (`B45Gen:883`), `stB45gL_of` (:906), `stWardTypePPingL_of` (:1018), `stB45PingL_of` (:1031) |
`open private`: none. No private deleted, no merged file edited, no RBM1D/RBM2D port (no `diff --stat` there). Imports of `B45BA`: `Chain.B45Gen`, `Chain.Step2Kern`, `BA.SEforLnBA` (brings `BA.KDecayBA`, `Chain.DecayGenTw`), `BA.KKernel`, `BA.KBase`, `BA.Ward`.
Final-name clash grep. The first run (06:14:08 UTC) used `\b`, which this platform's `git grep -E` does not support (probe on `t/T2486b`, run right after the valid grep: `^theorem baB45gL_of\b` finds nothing, `^theorem baB45gL_of([ :(]|$)` finds `B45BA.lean:240`), so that run is void. Valid run, 06:22:29 UTC, on `main`, `t/T2489`, `t/T2491`, `t/T2492`, `t/T2486`: declaration lines `^(private )?(theorem|def|lemma|abbrev|structure|instance) (baZeroModeGen_kerSums|baB45Gen_facts|baWardTypePgL_of|baB45gL_of|BAWardTypePPin|baWardTypePPin_holds|BAB45Pin|baB45Pin_holds)([ :(]|$)`, the namespace `B45BAInst`, the stem `B45BA_`, and file names `B45BA` in `RBM3D`: 0 hits on each; on `t/T2486b` (own) 37 hits (06:24:32 UTC), all in `RBM3D/BA/B45BA.lean`.
```
$ lake build RBM3D.BA.B45BA 2>&1 | tail -2         # 06:22:43 UTC, committed state
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (4099 jobs).
$ lake build 2>&1 | tail -3        # full library, worktree with the import line, 06:20:18-06:21:32 UTC (runs #assert_rbm_axioms), before the commit
non-vacuity certificates: 0 of 123 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4354 jobs).
exit=0
$ lake env lean docs/tickets/checks/T2486-check.lean     # 06:21:38 UTC, on the branch
exit=0 errors=0
$ wc -l RBM3D/BA/B45BA.lean      -> 399   (stop line 2,000 per file; C6 and split figures: part (a) report (1))
$ grep -cE 'sorry|admit|native_decide|^axiom ' RBM3D/BA/B45BA.lean   -> 0
$ lake env lean axioms.lean | sed -E "s/^'RBM\.BA\./'/"   # 06:22:43 UTC, #print axioms of the 8 public declarations and the 8 inst_ theorems (16 lines, abbreviated below)
'baZeroModeGen_kerSums' depends on axioms: [propext, Classical.choice, Quot.sound]
'baB45Gen_facts' ... 'baWardTypePgL_of' ... 'baB45gL_of' ... 'BAWardTypePPin' ... 'BAB45Pin' ... 'baWardTypePPin_holds' ... 'baB45Pin_holds'   (each: [propext, Classical.choice, Quot.sound])
'B45BAInst.inst_kerSums' ... 'inst_b45Facts' ... 'inst_wardTypePgL' ... 'inst_b45gL' ... 'inst_baWardTypePPin' ... 'inst_baB45Pin' ... 'inst_wardTypePPin_applied' ... 'inst_b45Pin_applied'   (each: [propext, Classical.choice, Quot.sound])
$ lake env lean axioms.lean 2>&1 | sed 's/.*depends on axioms: //' | sort | uniq -c       # 06:24:38 UTC
  16 [propext, Classical.choice, Quot.sound]
```
The module's only warnings are the style `longLine` ones on its module docstring (the `set_option` is placed after the docstring, as in `KDecayBA`, `SEforLnBA`).
### (4) Statement diff against the `T2486_*` pins (binding conclusions and classes)
```
$ python3 pindiff.py   # whitespace-normalized text of the check file's `T2486_X` body against the file's statement
T2486_BAKerSums vs baZeroModeGen_kerSums: IDENTICAL (whitespace-normalized) (117 chars)
T2486_BAB45Facts vs baB45Gen_facts: IDENTICAL (whitespace-normalized) (81 chars)
T2486_BAWardTypePPin vs BAWardTypePPin: IDENTICAL (whitespace-normalized) (208 chars)
T2486_BAB45Pin vs BAB45Pin: IDENTICAL (whitespace-normalized) (202 chars)
$ lake env lean pins.lean     # 06:22:11 UTC: the 4 check-file defs + imports of B45BA + 8 examples:
$                             # `example (d) : T2486_BAKerSums d := baZeroModeGen_kerSums d`, `T2486_BAB45Facts d := baB45Gen_facts d`,
$                             # `T2486_BAWardTypePPin d := baWardTypePPin_holds d` (and `fun R => baWardTypePPin_holds d R`), the same for `BAB45Pin`,
$                             # and the target-7 shape of the check file (as a Prop, and as a term proof from baWardTypePgL_of, baB45gL_of)
exit=0 examples=8
$ (the same file with `T2486_BAKerSums d := baB45Gen_facts d`)   -> error: Type mismatch  baB45Gen_facts d : B45Gen_Facts d ...   (a wrong example fails)
```
Target statements extracted from the file by script (`stmts.py`, truncated at 345 characters):
```
B45BA.lean:110: theorem baZeroModeGen_kerSums (d : ℕ) : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → ∀ n : ℕ, ZeroModeGen_KerSums (baFMz sz z) n
B45BA.lean:205: theorem baB45Gen_facts (d : ℕ) : B45Gen_Facts d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
B45BA.lean:226: theorem baWardTypePgL_of (d : ℕ) (hd : 3 ≤ d) (sz : Sizes d) (κ ε 𝔠 𝔡 Cd : ℝ) (z : ℕ → ℂ) (s t : ℕ → ℝ) (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (hs : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (hNt : ∀ᶠ n in atTop, (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - t n) (hD : STGdecayWgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd) : STWardTypePgL (baFMz sz z) ...
B45BA.lean:240: theorem baB45gL_of ... (same binders)  : STB45gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t
B45BA.lean:259: def BAWardTypePPin (d : ℕ) : Prop := ∀ (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop), STWardTypePPingL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)
B45BA.lean:265: def BAB45Pin (d : ℕ) : Prop := ∀ (R : ...), STB45PingL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)
B45BA.lean:272: theorem baWardTypePPin_holds (d : ℕ) : BAWardTypePPin d
B45BA.lean:282: theorem baB45Pin_holds (d : ℕ) : BAB45Pin d
```
### Compiled nonempty instances (namespace `B45BAInst`, `d = 3`, `sz0`, `zSeq`, `flow_sz0` at `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `s ≡ 1/2 < t ≡ 2/3 ≤ BAflowT0` by `t0_sz0`, `C_d = 1`)
```
$ grep -n "^theorem inst_\|^example" RBM3D/BA/B45BA.lean | cut -c1-150
314:theorem inst_kerSums (n : ℕ) : ZeroModeGen_KerSums (baFMz sz0 zSeq) n :=      -- baZeroModeGen_kerSums 3 sz0 .. flow_sz0 n
318:example : ∑ b, ‖Step2Gen_thetaKer (baFMz sz0 zSeq) 0 true false (1 / 2) 0 b‖ ≤ 1 / (1 - 1 / 2) :=   -- C₆ = 1, mixed pair, n = 0, t = 1/2
323:example : ‖∑ a, Step2Gen_thetaKer (baFMz sz0 zSeq) 0 false false (1 / 2) a 0‖ ≤ 1 / (1 - 1 / 2) :=   -- C₆ = 1, equal pair, column sum
329:theorem inst_b45Facts : ∃ C₆ : ℝ, 0 < C₆ ∧ ZeroModeGen_WardCls sz0 (baFMz sz0 zSeq) ∧ DecayGen_WardPair (baFMz sz0 zSeq) ∧ ... (all five fields at sz0)
339:theorem inst_wardTypePgL (hD : STGdecayWgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) 1) : STWardTypePgL ...
347:theorem inst_b45gL (hD : STGdecayWgL ...) : STB45gL ...
355:theorem inst_baWardTypePPin : STWardTypePPingL 3 STAny ... := baWardTypePPin_holds 3 STAny
360:theorem inst_baB45Pin : STB45PingL 3 STAny ... := baB45Pin_holds 3 STAny
367:theorem inst_wardTypePPin_applied (hLK : STLKgL (baFMz sz0 zSeq) .. (fun _ => 1 / 2)) (hStep2 : STStep2ConclgL (baFMz sz0 zSeq) .. (fun _ => 1 / 2) (fun _ => 2 / 3) 1) : STWardTypePgL ...
380:theorem inst_b45Pin_applied (hLK : ...) (hStep2 : ...) : STB45gL ...
```
Hypotheses left in the instances: `STGdecayWgL` (T1-BA's pin; `inst_wardTypePgL`, `inst_b45gL`), `STLKgL` and `STStep2ConclgL` (other gates' pins; `inst_*_applied`). Discharged at the data: `3 ≤ d`, `0 < κ`, `BAFlow` (`flow_sz0`), `0 ≤ s`, `t < 1`, `N⁻¹ ≤ 1 - t_n = 1/3` for every `n` (`N = (W L)^3 ≥ 3`, private `B45BAInst_inv_size`), `t ≤ BAflowT0` (`t0_sz0`), `STKboundgL` (`baKbound_holds`), `STKwardgL` (`baKward_holds`), `STConStInd` (`s1Setup_conStInd_const`, any `𝔠_d > 0`), `STKcalDecaygL` (`baKcalDecay_holds`). No `N = 0`, empty index set or `False` premise.
### (5) Hypotheses as used, copies
`baZeroModeGen_kerSums`, `baB45Gen_facts`: `0 < κ` and `BAFlow` only (no `0 < g₀`, no `0 < ε`). `baWardTypePgL_of`, `baB45gL_of`: `3 ≤ d`, `0 < κ`, `BAFlow`, `0 ≤ s`, `t < 1`, eventual `N⁻¹ ≤ 1 - t_n`, `STGdecayWgL`. The two pins and `_holds`: none, every regime `R` (by `by_cases 3 ≤ d`; for `d < 3` the setting `STIngRgL` has the premise `3 ≤ d`, so the pin is vacuous there, `intro h; exact absurd h hd`). Private helpers (stem `B45BA_`), re-derived here, not `open private`: `B45BA_Msigma_symm` follows `BAKBase_Msigma_symm` (`BA/KBase.lean:304`), `B45BA_Mss_norm_le` follows `BAKBase_norm_le` (`KBase:151`) and `BAKBase_norm` (`KBase:312`), `B45BA_norm_colsum_le` follows `B45_norm_colsum` (`Induction/B45.lean:781`) with `‖c‖ ≤ 1` in place of `‖μ‖ = 1`.
### (6) UBA-C1 table and greps (on `RBM3D/BA/B45BA.lean`)
Targets 6-8: no size-level/kernel-level crossing (the mollifier sits inside `B45Gen`; `thetaKer`, `Step2Kern_Mss` are at `g₀`); R1 not used, no comparison text.
```
C1  grep -nE '\|E\||norm_mE|mSigma|SB d|zt E|etaT|STFlow|STflowE|seqHflow [^B]|lemT'            -> 0 hits
    grep -n withLam | grep -v 'seqP (sz.withLam 0)\|seqP (sz0.withLam 0)'                        -> 1 hit, :17, the module docstring (`seqP ∘ withLam 0`)
    grep -nE 'gK|≤ A \*'                                                                           -> 0 hits
    grep -n STGridRepNgL                                                                           -> 0 hits
    grep -nE '(def|abbrev|structure) (ZeroModeGen_WardCls|ZeroModeGen_KerSums|Step2IterGen_OneLoop|STKcalDecaygL|SEforLnGen_Facts|B45Gen_Facts|Step5CasesGen_WardIdent|Step5CasesGen_FlowFacts)'  -> 0 hits
    grep -cE 'KLtreeValW|KLSigmaPi|kTwo|KLIsTSP|KLK_two|KLnodes|TSP'                               -> 0
Layering: grep -rn "import RBM3D.BA.B45BA" RBM3D RBM3D.lean -> RBM3D.lean:583 only (no Chain/* file imports it)
G1:  git diff main --stat -- RBM3D/Chain RBM3D/Induction RBM3D/Loop | wc -l  -> 0 ;  git diff main...t/T2486b --name-only -> RBM3D.lean, RBM3D/BA/B45BA.lean
```
### (7) Registry lines
`RBM3D/Test/Axioms.lean` is not touched (part (b) edits no owner text, ticket "Registry ... part (a) only"). The full `lake build` above, with the import line, passed `#assert_rbm_axioms`. Binder constants of the new public theorems that are Prop-valued `RBM` defs: `BAFlow` (concluded by `flow_sz0`), `STGdecayWgL` (registered, `Test/Axioms.lean:197`); the full build is the evidence that no unregistered remainder exists.
### Narrative
- Target 6 uses one argument for all four charge pairs: `Step2Kern_Mss * S` is `BAMss` (S = 1), translation invariant and symmetric, so its row and column sums are one constant `c`. This replaces the ticket's split (mixed pairs through `BAK`, equal pairs through shift and symmetry); the mixed pairs are the case `c = 1` (`BAMss_pm_eq`, `BAK_row_sum`).
- `C₆ = 1`: with `Q = M^{(σσ')}` and `|Q_ab| = BAK_ab` (unit row sums), `‖Q‖_{∞→∞} ≤ 1`; `Y = ΘQ` satisfies `Y = Q + tQY` (`BATheta_resolvent`), hence `‖Y‖ ≤ 1 + t‖Y‖ ≤ (1-t)⁻¹`, and `Σ_b |Y_ab| ≤ ‖Y‖`. No Neumann series. Column sums are `c(1-tc)⁻¹` with `|c| ≤ Σ_b BAK_{0b} = 1`.
- Everything reads `BAReal` at the given `n` (`BAflow_real`); no lemma with `0 < g` is used (part (a) report, row 11 trap).
- Target 8: the generic pins need `STKcalDecaygL` and the setting has `3 ≤ d →`; `by_cases 3 ≤ d` (row 13 trap).
## (c) Verified Mathlib names
Used and compiled: `Matrix.linfty_opNNNorm_def`, `Matrix.linfty_opNorm_mul`, `Fintype.sum_equiv`, `Finset.sup_le`, `NNReal.coe_sum`, `NNReal.coe_le_coe`, `norm_sub_norm_le`, `norm_add_le`, `norm_sum_le`, `norm_smul`, `Complex.norm_real`, `Real.norm_of_nonneg`, `inv_anti₀`, `le_div_iff₀`, `Nat.le_self_pow`, `Nat.le_mul_of_pos_left`, `Filter.Eventually.of_forall`. Absent or deprecated: none met.
## (d) Open issues and paper-delta candidates
- Hypotheses of other gates left in the instances: `STGdecayWgL`, `STStep2ConclgL` (T1-BA), `STLKgL` (stage-L pin).
- Candidate `T2486e`: paper `(eq:THETAinftinf)` `1_2:1141` bounds `‖Θ^{(σ₁,σ₂)}‖_{∞→∞} ≤ max_a Σ_b Θ^{(+,-)}_{t,ab} = (1-t)⁻¹` by an entrywise comparison; Lean proves `‖Θ M^{(σσ')}‖_{∞→∞} ≤ (1-t)⁻¹` (the kernel `thetaKer`, which is what `B45Gen_Facts` needs) by the resolvent identity and `‖M^{(σσ')}‖_{∞→∞} ≤ 1`, with the complex constant sums `c = Σ_b M_{ab}^2` (equal pairs) and `|c| ≤ 1` for the column sums. The same bound, a different route; no statement differs.
- Candidate `T2486f`: `BAWardTypePPin`, `BAB45Pin` are stated for all `d`; for `d < 3` they hold vacuously (`STIngRgL` has `3 ≤ d →`), the paper has `d ≥ 3` throughout.
