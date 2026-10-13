Prover model: claude-sonnet-5-5
# T2473c (T4s2c: `Chain/AzumaProxyGen`, targets 8-10) -- prove report, stage 1b of the third row of T2473
Branch `t/T2473c` (stacked on `t/T2473b` ce109b72; `RBM3D/Probe/T2473Pins.lean` stays on the stack and is never merged); worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2473c`. Binding: Amend 1, Amend 2 (`docs/tickets/T2473-amend-1.md`, `-amend-2.md`), supervisor 2351 T4S2-C2/C3, CONTROL H134 stop rule (`wc -l` at each section commit).

## (a) Math preflight
Not repeated: the stage-1a material of this row is `docs/reports/T2473-prove.md` ((a), (a″), (a‴)) and `docs/reports/T2473-1a-audit.md`. At the first `date -u` of this stage (Tue Oct 13 03:43:07 UTC 2026) `ls docs/reports | grep T2473` (03:43:26) printed `T2473-1a-audit.md T2473-audit.md T2473-prove.md T2473b-audit.md T2473b-prove.md`: no `T2473c-prove.md` existed, so this file has no section (a) of its own.

## (a′) Preflight corrections -- Tue Oct 13 04:41:49 UTC 2026
One route correction, no verdict change. Ticket target 10 and `T2473-prove.md` (a) (i) say the row sum of the `Step2Gen_UN` kernel follows from K2. K2 needs `v ≤ w`; the public form `AzumaProxyN_rowsum_UN_pubg` (like the band `AzumaProxyN_rowsum_Ugen_pub`, `0 ≤ v, w < 1`, no order) takes K3 (`Σ_b ‖uKer_{v,w}(a,b)‖ ≤ 1 + |w - v| (1 - w)⁻¹ ≤ 1 + (1 - w)⁻¹`) through the one-slot bound `GridAssemblyGen_row_le`, as `T2473b-prove.md` (a′) did for the coarse bound. The kernel class is still T2471's single text `GridRepTailGen_Ker`; nothing is added.

## (b) Script output
```
$ TZ=UTC git log --format='%h %cd %s' --date=format-local:'%a %b %d %H:%M:%S UTC %Y' ce109b72..HEAD | grep "T2473c:"   (cut to 120 columns)
61732d61 Tue Oct 13 04:22:26 UTC 2026 T2473c: merge main (T2483b, T2485) into t/T2473c
013e0fd8 Tue Oct 13 04:16:40 UTC 2026 T2473c: merge main (T2482 and docs) into t/T2473c
642bc03b Tue Oct 13 04:10:02 UTC 2026 T2473c: AzumaProxyGen rename the eta public form (no etaT in generic names)
c2d85e38 Tue Oct 13 04:08:12 UTC 2026 T2473c: AzumaProxyGen compiled nonempty instances (targets 8-10) and registry line
cb5e2370 Tue Oct 13 04:01:40 UTC 2026 T2473c: AzumaProxyGen band bridge and band corollaries (target 11, no instances ye
b5dbaaef Tue Oct 13 03:58:26 UTC 2026 T2473c: AzumaProxyGen weighted Y fields, yMomentsUnifNg, yMomentsNg, public helper
8b084bc2 Tue Oct 13 03:51:36 UTC 2026 T2473c: AzumaProxyGen azumaSubGNg, compositions, exit-time positivity (targets 8, 
f54a2573 Tue Oct 13 03:43:27 UTC 2026 T2473c: merge main into t/T2473c
$ stop rule (CONTROL H134): `wc -l RBM3D/Chain/AzumaProxyGen.lean` printed at the four section commits 8b084bc2, b5dbaaef, cb5e2370, c2d85e38 (tool log): 245, 643, 741, 950   (stop size 2,000)
$ date -u; git log --oneline -1; wc -l RBM3D/Chain/AzumaProxyGen.lean
Tue Oct 13 04:41:49 UTC 2026
61732d61 T2473c: merge main (T2483b, T2485) into t/T2473c
     950 RBM3D/Chain/AzumaProxyGen.lean
$ lake build RBM3D.Chain.AzumaProxyGen   (04:10:02 UTC, after the last edit of the file; a build with a warning prints ⚠)
✔ [3872/3872] Built RBM3D.Chain.AzumaProxyGen (9.5s)
Build completed successfully (3872 jobs).
$ lake build   (04:22:26-04:24:29 UTC, after the merge of main 2cc78196; RBM3D.lean does not import the module, the hub adds the import line)
info: RBM3D.lean:574:0: axiom audit: 14511 theorems, 4545 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4342 jobs).
$ lake env lean root_check.lean   (a copy of RBM3D.lean with `import RBM3D.Chain.AzumaProxyGen` after the last import line; 04:24:35-04:26:47 UTC) ; same for root_base.lean (RBM3D.lean unchanged)
base-exit=0  check-exit=0
axiom audit: 14511 theorems, 4545 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
axiom audit: 14528 theorems, 4547 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ diff root_base.out root_check.out | grep -E "^[<>]" | cut -c1-120   (the premise scan: `GoodSetNg` is found, registered by the line added to `RBM3D/Test/Axioms.lean`)
< axiom audit: 14511 theorems, 4545 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
> axiom audit: 14528 theorems, 4547 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
<   RBM.BA.GoodSetNg: 1 [no certificate]
>   RBM.BA.GoodSetNg: 3 [no certificate]
< premises found by scanning: 126 (borrowed 1, owed 59, structural 46, refuted 6, superseded 14).
< registry: 2 borrowed + 119 owed + 123 structural + 7 refuted + 18 superseded; 143 registered premise(s) carry nothing 
> premises found by scanning: 127 (borrowed 1, owed 60, structural 46, refuted 6, superseded 14).
> registry: 2 borrowed + 119 owed + 123 structural + 7 refuted + 18 superseded; 142 registered premise(s) carry nothing 
<  RBM.BA.GoodSetNg,
$ lake env lean pins_ax.lean   (scratch copy of the file: the 18 `example`s renamed `instN` as `def`, one `#print axioms` per declaration: 19 public declarations + 18 examples)
37 names; 18 examples
  37 depends on axioms: [propext, Classical.choice, Quot.sound]
$ python3 stmt2.py ...   (hypotheses and conclusions of the public theorems, extracted from the file; hypotheses cut to 150, lines to 330 columns)
theorem azumaSubGNg (line 87)
  hypotheses: [IsProbabilityMeasure Cm.Pp] | (hW : StepDecompGen_WalkForm Cm lam' Ψ)
  conclusion: AzumaSubGNg Cm lam' s t K
theorem azumaProxy_Hpath_zerog (line 136)
  hypotheses: (hW : StepDecompGen_WalkForm Cm lam' Ψ) | (hs : s n = 0)
  conclusion: Cm.Hpath s t K n 0 ω = Ψ n
theorem azumaProxy_pos_gridExitTauNg (line 147)
  hypotheses: (hK : 0 < K n) | (h0 : Cm.Hpath s v K n 0 ω ∈ G 0)
  conclusion: 0 < gridExitTauNg Cm s v K n G ω
theorem azumaProxy_pos_goodExitTauNg (line 164)
  hypotheses: (hK : 0 < K n) | (h0 : GoodSetNg Cm n (gridTime s v K n 0) k (Γ n) (Λ n) (Φ n) τ' D' (Cm.Hpath s v K n 0 ω))
  conclusion: 0 < goodExitTauNg Cm s v K k Γ Λ Φ τ' D' n ω
theorem azumaProxy_subG_ugeng (line 193)
  hypotheses: [IsProbabilityMeasure Cm.Pp] | (h : AzumaSubGNg Cm g s t K) | (hL : StepDecompGen_LoopForm Cm E) | (hQV : QVPropagatedNg Cm g) | (hs0 : ∀ n, 0 ≤ s n) | (hst : ∀ n, s n ≤ t n) | (ht1 : ∀ n, t n < 1) | (hKer : GridRepTailGen_Ker Cm.toFlowFM n) | (hk : 2 ≤ k) | (hG : ∀ ω j, j < τ ω → Cm.Hpath s t K n j ω ∈ G j) | (hm 
  conclusion: SubGaussStopNg Cm σ (gridTime s t K n) τ (fun j ω => ZvecNg Cm s t K n j σ ω) m a j Q
theorem azumaProxy_subG_goodExitg (line 230)
  hypotheses: [IsProbabilityMeasure Cm.Pp] | (h : AzumaSubGNg Cm g s v K) | (hL : StepDecompGen_LoopForm Cm E) | (hW : StepDecompGen_WalkForm Cm lam' Ψ) | (hQV : QVPropagatedNg Cm g) | (hs0 : ∀ n, 0 ≤ s n) | (hsv : ∀ n, s n ≤ v n) | (hv1 : ∀ n, v n < 1) | (hKer : GridRepTailGen_Ker Cm.toFlowFM n) | (hk : 2 ≤ k) | (hm : m ≤ K n) 
  conclusion: SubGaussStopNg Cm σ (gridTime s v K n) (goodExitTauNg Cm s v K k Γ Λ Φ τ' D' n) (fun j ω => ZvecNg Cm s v K n j σ ω) m a j Q
theorem AzumaProxyN_YfieldsWg (line 462)
  hypotheses: (hL : StepDecompGen_LoopForm Cm E) | (hW : StepDecompGen_WalkForm Cm lam' Ψ) | (hst : s n ≤ t n) | (ht1 : t n < 1) | (hj : j + 1 ≤ K n) | (hS0 : 0 ≤ Smax) | (hC20 : 0 ≤ C2) | (hrow : ∑ c, ‖κ c‖ ≤ Smax) | (hC2 : ∀ (a : Fin k → Zd d (sz.L n)) (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), M.IsH
  conclusion: Cm.Pp[fun ω => (AzumaProxyN_stopWg Cm s t K n j σ κ τ ω).re | filt sz j] =ᵐ[Cm.Pp] 0 ∧ Cm.Pp[fun ω => (AzumaProxyN_stopWg Cm s t K n j σ κ τ ω).im | filt sz j] =ᵐ[Cm.Pp] 0 ∧ Integrable (fun ω => (AzumaProxyN_stopWg Cm s t K n j σ κ τ ω).re ^ 4) Cm.Pp ∧ Integrable (fun ω => (AzumaProxyN_stopWg Cm s t K n j σ κ τ ω).
theorem AzumaProxyN_c0_pos_pubg (line 503)
  hypotheses: (h : DecayGen_Spec C κm)
  conclusion: 0 < κm
theorem AzumaProxyN_eta_inv_le_pubg (line 507)
  hypotheses: (h : DecayGen_Spec C κm) | (hut : u ≤ t) | (hN0 : 0 < N) | (hR : N ^ (-1 + τ') ≤ 1 - t)
  conclusion: (C.eta n u)⁻¹ ≤ N ^ (1 - τ') / κm
theorem AzumaProxyN_rowsum_UN_pubg (line 524)
  hypotheses: (hK : GridRepTailGen_Ker C n) | (hv0 : 0 ≤ v) | (hv1 : v < 1) | (hw0 : 0 ≤ w) | (hw1 : w < 1)
  conclusion: ∑ b : Fin k → Zd d (sz.L n), ‖∏ i : Fin k, Step2Gen_uKer C n (σ i) (σ (finRotate k i)) v w (a i) (b i)‖ ≤ (1 + (1 - w)⁻¹) ^ k
theorem yMomentsUnifNg (line 558)
  hypotheses: (hL : StepDecompGen_LoopForm Cm E) | (hW : StepDecompGen_WalkForm Cm lam' Ψ) | (hKer : ∀ n, GridRepTailGen_Ker Cm.toFlowFM n)
  conclusion: YMomentsUnifNg Cm κm τ' s t
theorem yMomentsNg_of_unif (line 624)
  hypotheses: (h : YMomentsUnifNg Cm κm τ' s t)
  conclusion: YMomentsNg Cm κm τ' s t K
theorem yMomentsNg (line 632)
  hypotheses: (hL : StepDecompGen_LoopForm Cm E) | (hW : StepDecompGen_WalkForm Cm lam' Ψ) | (hKer : ∀ n, GridRepTailGen_Ker Cm.toFlowFM n)
  conclusion: YMomentsNg Cm κm τ' s t K
$ python3 pindiff4.py   (definitions vs the probe texts `RBM3D/Probe/T2473Pins.lean`, docstrings excluded; the other pins of targets 7-10 are T4s2b's)
IDENTICAL YMomentsUnifNg
IDENTICAL AzumaSubGNg
IDENTICAL YMomentsNg
$ python3 inst4.py   (the compiled nonempty instances of section 5 and the first lines of their statements)
L785-785  example : sz0.L 0 = 4 ∧ sz0.W 0 = 32 ∧ sz0.size 0 = 2097152 ∧ Kg 0 = 4 ∧ gridStep sInst vg Kg 0 = 1 / 128
L792-793  theorem azumaSubGNg_instance (m : ℕ) (a : Fin 3 → Zd 3 (sz0.L 0)) : SubGaussFormNg Cm0 0 (fun _ => Kg 0) (fun ω => ∑ b, kap3 m a b * ZfamNg Cm0 sInst vg Kg 0 0 phi3 
L802-802  example : 0 < qProxy3 1 b0
L805-805  example (ω : PathΩ sz0) : Cm0.Hpath sInst vg Kg 0 0 ω = 0
L808-808  example (ω : PathΩ sz0) : 0 < gridExitTauNg Cm0 sInst vg Kg 0 (fun _ => {H | H.IsHermitian}) ω
L821-821  example (ω : PathΩ sz0) : 0 < goodExitTauNg Cm0 sInst vg Kg 3 Γ4 Λ3 Φ1 (1 / 2) 1 0 ω
L826-830  example (m : ℕ) (hm : m ≤ Kg 0) (hj : 0 < m) (a : Fin 3 → Zd 3 (sz0.L 0)) : SubGaussStopNg Cm0 sig3 (gridTime sInst vg Kg 0) (fun _ => Kg 0) (fun j ω => ZvecNg Cm0 s
L843-848  example (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ) (m : ℕ) (hm : m ≤ Kg 0) (hj : 0 < m) (a : Fin 3 → Zd 3 (sz0.L 0)) (Q : ℝ≥0) (hQ : ∀ M, GoodSetNg Cm0 0 (gridTime sInst vg Kg 0 0)
L853-853  example : 0 < Real.sqrt 1 / 2
L855-855  example : (Cm0.eta 0 (1 / 4))⁻¹ ≤ (4 : ℝ) ^ (1 - (1 / 2 : ℝ)) / (Real.sqrt 1 / 2)
L861-862  example : ∑ b : Fin 3 → Zd 3 (sz0.L 0), ‖∏ i : Fin 3, Step2Gen_uKer Cm0.toFlowFM 0 (sig3 i) (sig3 (finRotate 3 i)) (1 / 128) (1 / 32) ((fun _ => (0 : Zd 3 (sz0.L 0))
L868-873  theorem yMomentsUnifNg_instance (σ : Fin 3 → Bool) : ∃ C_P : ℝ, 0 ≤ C_P ∧ ∃ n : ℕ, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz0.size n : ℕ) : ℝ) ^ C_P ∧ 0 < gridStep sInst vg Kg n ∧ Y
L880-885  example (σ : Fin 3 → Bool) : ∃ C_P : ℝ, 0 ≤ C_P ∧ ∃ n : ℕ, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz0.size n : ℕ) : ℝ) ^ C_P ∧ 0 < gridStep sInst vg Kg n ∧ YMomentBoundsNg Cm0 σ (gr
L893-904  example (σ : Fin 3 → Bool) : ∃ n : ℕ, ∃ P : ℝ, 0 ≤ P ∧ 0 < gridStep sInst vg Kg n ∧ YMomentBoundsNg Cm0 σ (gridTime sInst vg Kg n) (fun _ => Kg n) (Kg n) (fun j ω =>
L917-918  theorem yfieldsWg_instance (κ : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ) : let C2 : ℝ
instances: 15
$ clash6.sh   (`git grep -w` of the 19 new public names and the stems `AzumaProxyGen`, `AzumaProxyGenCheck`, `AzumaProxyGen2` on main and every t/T24* branch; the hit lines are printed)
refs:      100 (main + t/T24* except t/T2473c); names:       22; RBM3D/Probe/T2473Pins.lean excluded
name/location azumaSubGNg RBM3D/Chain/GridAssemblyGen.lean:1000: 7 refs: main t/T2473b t/T2482b t/T2484b t/T2485 t/T2487 t/T2488
name/location azumaSubGNg RBM3D/Chain/GridAssemblyGen.lean:420: 7 refs: main t/T2473b t/T2482b t/T2484b t/T2485 t/T2487 t/T2488
name/location azumaSubGNg RBM3D/Chain/GridAssemblyGen.lean:1099: 7 refs: main t/T2473b t/T2482b t/T2484b t/T2485 t/T2487 t/T2488
declaration hits (theorem|def|structure|abbrev|namespace of a new name):        0
$ grep -nE "def .*[Kk]er\b|def Ugen" ; grep -n STGridRepNgL ; grep -n "^import RBM3D.BA" ; grep -nwE "sorry|admit|native_decide|axiom"   (the file; importers of AzumaProxyGen in RBM3D, RBM3D.lean)
(no hit above this line)
$ python3 x1c1_4.py   (hypothesis-rule grep of the ticket, hit lines classified)
docstring: L21,33,72,86,134,461,505,521,542,696
W: proof of a theorem that takes hW (pathP/pathH at sz.withLam lam'): L78,91,98,100,141,142,483,486
private core at an abstract walk P (instantiated only at sz.withLam lam'): L268,271,272,273,274,275,276,277,278,279,281,296,298,300,308,315,316,319,324,326,329,340,344,346,353,366,368,371,372,373,376,377,390,395,399,403
band bridge / band corollary (statement of a merged band theorem): L664,668,693,697,705,723
band instance (sz0, Einst): L796,809,833
hits in a public generic statement text: 0 (all docstring, proof, private core, band bridge or instance)
$ grep -nE "withLam|BAflowLam0|gK" (the file): hit lines
20 21 78 85 86 91 96 97 111 113 120 124 142 460 461 483 486 487 492 
(docstrings: 20, 21, 85, 86, 460, 461; every other hit is inside the proof of a theorem that takes `hW : StepDecompGen_WalkForm`, or the call of the private core at `sz.withLam lam'`; no crossing of `sz.lam` with a kernel or a coupling)
$ grep -nE "InitMem|zero_mem_goodSet" (the file) | cut -c1-110
26:  `zero_mem_goodSetN_of_levels`; BA: owed to T4-BA).
163:band `zero_mem_goodSetN_of_levels` (`AzumaProxyN:924`) at `s n = 0` with `azumaProxy_Hpath_zerog`; BA: owe
746:band lemma `zero_mem_goodSetN_instance_grid`; the majorant `hQ` of `azumaProxy_subG_goodExitg` on the good
812:`D' = 1`, `k = 3`: the **band discharge of the inline hypothesis of target 9** (`zero_mem_goodSetN_instanc
817:  exact (bandStep2_GoodSetN sz0 Einst 0 _ 3 _ _ _ (1 / 2) 1 0).1 zero_mem_goodSetN_instance_grid
$ grep -n "^open private" -A2 (the file); the opened names and their band lines
42:open private azumaProxy2_condExp_incr azumaProxy2_measurable_normX azumaProxy2_moments_of_dom
43-  azumaProxy2_condExp_stopped_reim azumaProxy2_gridStep_nonneg azumaProxy2_gridTime_nonneg azumaProxy2_gridTime_le
44-  from RBM3D.Induction.AzumaProxyN2
45:open private GridAssemblyGen_row_le from RBM3D.Chain.GridAssemblyGen
46-
47-open MeasureTheory ProbabilityTheory Filter
395:private theorem azumaProxy2_condExp_incr (j : ℕ) {φ : Sizes.SeqΩ s
389:private theorem azumaProxy2_measurable_normX (n : ℕ) :
414:private theorem azumaProxy2_moments_of_dom (n j : ℕ) {W : PathΩ sz
493:private theorem azumaProxy2_condExp_stopped_reim (j : ℕ) {S : Set 
618:private theorem azumaProxy2_gridStep_nonneg {s t : ℕ → ℝ} {K : ℕ →
622:private theorem azumaProxy2_gridTime_nonneg (s t : ℕ → ℝ) (K : ℕ →
630:private theorem azumaProxy2_gridTime_le (s t : ℕ → ℝ) (K : ℕ → ℕ) 
225:private theorem GridAssemblyGen_row_le {C : FlowFM sz} {n : ℕ} (hK
$ git diff main...HEAD --name-only ; (forbidden files) | wc -l ; --stat
RBM3D/Chain/AzumaProxyGen.lean
RBM3D/Probe/T2473Pins.lean
RBM3D/Test/Axioms.lean
       0
 RBM3D/Chain/AzumaProxyGen.lean | 950 +++++++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2473Pins.lean     | 400 +++++++++++++++++
 RBM3D/Test/Axioms.lean         |   1 +
 3 files changed, 1351 insertions(+)
$ ports
none copied from ../RBM1D or ../RBM2D; sources: RBM3D/Induction/AzumaProxyN.lean (last commit 37426e67) and RBM3D/Induction/AzumaProxyN2.lean (last commit 88183f42), ported to the carrier; the band files are not edited.
```
Narrative.
(1) Delivered: `RBM3D/Chain/AzumaProxyGen.lean`, 950 lines against the stop size 2,000. Target 8: `azumaSubGNg` (:87), `azumaProxy_Hpath_zerog` (:136), `azumaProxy_pos_gridExitTauNg` (:147), `azumaProxy_subG_ugeng` (:193), `azumaProxy_subG_goodExitg` (:230). Target 9: `azumaProxy_pos_goodExitTauNg` (:164), whose initial membership `h0` is an inline hypothesis. Target 10: the pin `YMomentsUnifNg` (:544), `AzumaProxyN_stopWg` (:452), `AzumaProxyN_YfieldsWg` (:462), `yMomentsUnifNg` (:558), `yMomentsNg_of_unif` (:624), `yMomentsNg` (:632), the public forms `AzumaProxyN_c0_pos_pubg` (:503), `AzumaProxyN_eta_inv_le_pubg` (:507), `AzumaProxyN_rowsum_UN_pubg` (:524); the other two `_pub` forms of the band are model-free and are reused unchanged. Section 4 (:641) holds `bandStep2_AzumaSubGN` and six band corollaries; section 5 (:739) the instances. Target 6 is T2474's, targets 1-5 and 7 are on `main`.
(2) Texts: W, LoopForm and `QVPropagatedNg` (the S class) are T2474's, `GridRepTailGen_Ker` is T2471's, the pins `AzumaSubGNg`, `YMomentsNg` are T4s2b's and are unchanged. The only new pin is `YMomentsUnifNg`, identical to the probe text (script above); `AzumaProxyN_stopWg` is the vocabulary `def` of the band. No named `Prop`, no kernel, no `FlowFM`/`Step2Mat` field was added.
(3) `azumaSubGNg` is the band `azumaSubGN` at `sz.withLam lam'` for the family `M ↦ Φ_b (Ψ n + M)` (`StepDecompGen_hermTestFun_shift`, `_withLam`), the sets `{M | Ψ n + M ∈ G_j}`, a shift lemma for `dirDerivN` and `StepDecompGen_hcsg_of_withLam` for the law; it reads W only. `azumaProxy_subG_ugeng` does not read W: it reads the pin `h`, LoopForm (`HermTestFun` of `loopFamNg` by `hermTestFunLoopNOf`), `QVPropagatedNg` and K4 (`qvFormNg = Re Σ κ κ̄' STeeMg`, private `AzumaProxyGen_qvForm_eq`); `azumaProxy_subG_goodExitg` adds W for `goodExitMeasNg`.
(4) Y moments: the private core `AzumaProxyGen_YfieldsW_core` (:259) is the body of the band `AzumaProxyN_YfieldsW` for an abstract walk `P : Sizes d`, a test family `Φ` and a remainder `Yv` that is a.e. `stepYCN` of the identity kernel; `AzumaProxyN_YfieldsWg` applies it at `P = sz.withLam lam'`, `Φ = loopFamNgShift Cm Ψ …`, `Yv = YvecNg` (`YvecNg_eq_stepYCN`, `GridAssemblyGen_stronglyMeasurable_YvecNg`). The eight fields of `YMomentBoundsNg` in `yMomentsUnifNg` are the weighted fields with `κ c = Π_i uKer(b_i, c_i)` (`stoppedEdgeNg` is the indicator of `Step2Gen_UN … (Y_j) b`), so the band's one-label lemma `azumaProxy2_Yfields` is not ported. `C_P = 11 + (4k+4) max 0 (1 - τ')` and `P = 2000 (S C₂)² N⁸` as in the band, with `c₀ := κm` of `DecayGen_Spec`, `S = (2 N^θ)^k` from K3, `C₂` from `StepDecompGen_loopFamShift_hermTestFun`.
(5) Target 9 and the registry: the band discharge of `h0` is the private instance lemma `h0_inst` (`zero_mem_goodSetN_instance_grid`, `bandStep2_GoodSetN`, `azumaProxy_Hpath_zerog`). This file has no BA reading and no `BA/*` import (supervisor 2351 T4S2-C2/C3); the BA initial membership is owed to T4-BA. The premise scan found `GoodSetNg` (hypotheses `h0` and `hQ`); one `owedProps` line was added to `RBM3D/Test/Axioms.lean`, and the root check above passes with it.
(6) Band corollaries (section 4, `example`s): `AzumaSubGN`, `azumaProxy_subG_ugen`, `azumaProxy_pos_gridExitTauN`, `azumaProxy_pathH_zero_of_s_zero`, `YMomentsUnifN`, `YMomentsN`, from the generic theorems at `bandStep2Mat sz E` with LoopForm, W, K1-K4, `qvPropagatedNg` and `DecayGen_bandSpec` (`κm = √κ/2`) discharged by the band lemmas.
(7) `open private`: seven grid-arithmetic and moment helpers of `AzumaProxyN2` and `GridAssemblyGen_row_le` of T4s2b (precedent `Chain/B45Gen.lean:44`); none for an S2 or LoopForm BA reading.
(8) Instances (section 5): `sz0`, `Einst ≡ 1/2`, `(s, t, K) = (0, 1/32, 4)`, `Δ = 1/128`, `k = 3`, `σ = (+,-,+)`; every deterministic hypothesis is discharged. Open in one example: the majorant `hQ` on the good set in the `azumaProxy_subG_goodExitg` example (Step 3, another gate's output, as in the band instance `azumaSubGN_goodExit_instance`). The Y-moment examples apply the eventual statement at an `n` taken from the filter (`Filter.Eventually.exists`), as the band instances do; `azumaSubGNg_instance` has the positive proxy of `qProxy3_pos` at `m = 1`, `a = (0,0,0)`.
(9) Stop rules checked: file 950 < 2,000; the pin `YMomentsUnifNg` equals the probe text; no premise outside D2 and (a) (i); no new `FlowFM`/`Step2Mat` field, third kernel or `BA/*` import; no edit of `Induction/*`, `Path/*`, `BA/*`, `Chain/{Carrier,Step2Gen,Step2Kern,GridDuhamelGen,DecayGen,Step34Gen,StepDecompGen,Step2EventsGen,HierDriftGen,GridRepTailGen*,GridGoodGen,GridEnvelopeGen,GridAssemblyGen}` (diff 0 lines). `main` moved during the stage (ba7e559e to 2cc78196; three merges above); `git diff ba7e559e 2cc78196 --name-only -- RBM3D RBM3D.lean` lists `BA/Step5IIIEdet.lean`, `BA/Step5IIIGood.lean`, `BA/Step5IIIGood2.lean`, `Graph/BAMomentExpGenB.lean`, `RBM3D.lean` and `Test/Axioms.lean` (one registry line, merged without conflict); none of the first four is imported by the file.

## (c) Verified Mathlib names (resolved by script in the module environment of the file; used in the file, compiled)
`Complex.abs_im_le_norm`, `Complex.abs_re_le_norm`, `Complex.measurable_im`, `Complex.measurable_re`, `Finset.card_univ`, `Finset.measurable_sum`, `Finset.prod_const`, `Finset.prod_le_prod₀`, `Finset.sum_apply`, `Finset.sum_ite_eq`, `Finset.sum_le_sum`, `Finset.sum_mul`, `Finset.sum_nonneg`, `Fintype.card_fin`, `Fintype.prod_sum`
`MeasurableSet.const`, `MeasureTheory.hittingBtwn_le_iff_of_lt`, `MeasureTheory.ae_all_iff`, `MeasureTheory.condExp_congr_ae`, `MeasureTheory.condExp_finsetSum`, `MeasureTheory.condExp_smul`, `MeasureTheory.integrable_const`, `MeasureTheory.integral_const_mul`, `MeasureTheory.integral_nonneg`
`Real.le_coe_toNNReal`, `Real.one_le_rpow`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_le_rpow_of_nonpos`, `Real.rpow_mul`, `Real.rpow_neg`, `Real.rpow_pos_of_pos`, `Set.indicator_of_notMem`, `Filter.eventually_ge_atTop`, `Nat.le_of_not_lt`, `Nat.pos_of_ne_zero`, `Nat.zero_lt_one`
`inv_anti₀`, `inv_inv`, `inv_nonneg`, `mul_inv`, `div_eq_mul_inv`, `div_pos`, `map_prod`, `norm_prod`, `norm_sum_le`, `norm_indicator_le_norm_self`, `pow_le_pow_left₀`, `measurable_pi_apply`, `mul_le_mul`, `mul_le_mul_of_nonneg_left`, `mul_le_mul_of_nonneg_right`, `lt_of_lt_of_le`
No name was found absent; the build line above is ✔ (no warning from the file).

## (d) Open issues and paper-delta candidates
- Hub: add `import RBM3D.Chain.AzumaProxyGen` after the last import line of `RBM3D.lean` at merge (CLAUDE.md §1, §3 (A) 4; the run prompt mentions the root import line, but `RBM3D.lean` is the hub's file and is not edited here, as for T4s2a and T4s2b). Merge after T4s2b (on `main` since 4efcae69); the file imports `Chain/GridGoodGen` (86eb22f2), `Chain/GridAssemblyGen` (4efcae69) and `Induction/AzumaProxyN2`.
- Registry class for the dispatcher: the ticket expected only the three T4s2a lines; the scan also reports `GoodSetNg` and I classed it `owedProps` (initial membership: owner T4-BA; `hQ`: Step 3, U3s2-U3s3). The alternative is `structuralProps` (a predicate that defines the good set).
- BA owed items unchanged: the initial membership (target 9, T4-BA); `0 < Im m` of `baStep2Mat_loopForm`; `QVPropagatedNg` at BA (`Cm.S n = SB … (g n)`, `g = 0`); K1-K4 at BA is the merged `gridRepTailGen_ker_BA`. The BA readings of the pins typechecked in the 1a probe (`RBM3D/Probe/T2473Pins.lean:394-395`, `T2473-prove.md` (a″)); they are not recompiled here (no `BA/*` import in a `Chain` file).
- T2473j: the compositions take the S class `QVPropagatedNg Cm g` and `hKer` (K4 gives `qvFormNg = Re Σ κ κ̄' STeeMg`) in place of the band's `qvPropagatedN` and `hE : |E n| < 2`; `azumaProxy_subG_ugeng` does not read W, `azumaProxy_subG_goodExitg` does (for `goodExitMeasNg`).
- T2473k: `AzumaProxyN_YfieldsWg` drops the band premises `0 ≤ s n` and `|E n| < 2` (not read: `hermTestFunLoopNOf` needs `u < 1`); `hC2` bounds the second derivative of `loopFamNgShift Cm Ψ …` (the loop family seen from the shifted walk).
- T2473l: `yMomentsUnifNg` takes `c₀ := κm` of `DecayGen_Spec` in place of `√(κ(4 - κ))/2`; `C_P` is the band's; the band corollary uses `κm = √κ/2`, so the explicit `P` differs and the `∃ P` statements agree.
- T2473m: `AzumaProxyN_rowsum_UN_pubg` uses K3, not K2 (as T2473g); `AzumaProxyN_eta_inv_le_pubg` is the generic form of `AzumaProxyN_etaT_inv_le_pub` (renamed so that no generic name contains `etaT`); `AzumaProxyN_c0_pos_pubg` is `DecayGen_Spec.1`.
- T2473n: target 9 is the inline hypothesis `h0` of `azumaProxy_pos_goodExitTauNg` (no named `Prop`); `azumaSubGNg` carries `[IsProbabilityMeasure Cm.Pp]` as the pin does (derivable from W).
