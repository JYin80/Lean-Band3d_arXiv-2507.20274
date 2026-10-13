Prover model: claude-sonnet-5-5

## (a) Math preflight: not repeated
Row b (L5b + L6 + target 9) has no stage 1a of its own. Its section (a) is `docs/reports/T2494-prove.md` lines 3-80 (written Tue Oct 13 07:28:30 UTC 2026; verdict PASS; cut A | B + C; switch (a) to prover-max holds). Fill-in table (§269 (5)): (i) :9-22, (ii) :24-38, (iii) :40-64, (iv) :64, (v) :66-68, (vi) :70-74. Row a (file A, merged 1843bd31) is `T2494-prove.md` (b) from line 82.

## (a′) Preflight corrections — Tue Oct 13 09:16:20 UTC 2026
- (ii) R8, constants of the `T` side: (a) carries the band numbers `Γ = X²`, `K0 = 165646`. At BA the two `≺` of `(eq:directG2)` (`baGbyZeta_holds`, `baZetaExpClaim_holds`) compose by `StochDomAt.trans` and cost one factor `N^{τ/6}`, so `Γ = X = N^{τ/6}`; the threshold is `K0 ≤ X` with `K0 = 4 K1 + 2 K2`, `K1 = 6 + 16cB + 2(4 + 8cB)cs` (= 165646 at `Λ = 𝔡⁻¹ = 10`, `cB = cs = 1 + Λ²`: the number of (a)), `K2 = cs Kz (4 + 32cB + 8 Kz cB)`, `Kz = C' E` (the M-part constant, `BAMomentGen_consts` and `BATermHoldsB_sfMb`). Eventual in `n` at fixed `τ`: no slack changes, no verdict changes.
- (v) census: (a) predicted B = 1,057, C = 140 lines; delivered 1002 and 126 (below).

## (b) Script output, row b (files B + C, target 9, root imports); stage 1b `prover-max` — written Tue Oct 13 09:16:20 UTC 2026
Start decision: row b starts after row a's audit PASS (merge 1843bd31) and after T2489b (L4b2b) merged (bbe91c0a); branch `t/T2494b` stacked on `t/T2494` (e50823fe), `main` merged in first (5f7316cb). Stop rule H134: `wc -l` at every commit that touches B or C is in the first block (stop line 2,000).
```
$ date -u; git log --oneline 5f7316cb..HEAD (the commits of row b)
Tue Oct 13 09:14:24 UTC 2026
49855655 T2494b: compiled emptiness of the regime 1 - t <= lam^2/L^2 at the merged flow data for every admissible t
6f803570 T2494b: instances of targets 4, 5 at the range ell = ell_t (not a collapsed window)
b803ced6 T2494b: BATermHoldsB header docstring rewrapped
db957998 T2494b: docstring line citations of BATermHoldsB, BALWOut corrected
e6bffe09 T2494b (target 9): registry lines of BALWterm, BALWtermExp removed, owner texts; root imports of BATermHoldsB, BALWO
45108b9c T2494b (L6): Graph/BALWOut: baLWCutExpTw_holds, baLWtermEXPTw_holds, instances
22834138 T2494b (L5b): Graph/BATermHoldsB: baLWtermExpS_holds, baLWtermExp_holds, baStep2_closed, instances
$ git merge-base --is-ancestor bbe91c0a main; git merge-base --is-ancestor 1843bd31 HEAD; git rev-parse --short main t/T2494 (one per line)
T2489b merge bbe91c0a is an ancestor of main
row a merge 1843bd31 is an ancestor of HEAD
main 035c4b84
t/T2494 e50823fe
$ wc -l B C (stop line 2,000 per file) at every commit that touches them: git show <hash>:<file> | wc -l
BATermHoldsB.lean 22834138      947
BATermHoldsB.lean db957998      947
BATermHoldsB.lean b803ced6      947
BATermHoldsB.lean 6f803570      966
BATermHoldsB.lean 49855655     1002
BALWOut.lean 45108b9c      126
BALWOut.lean db957998      126
$ wc -l B C; grep -nE "sorry|admit|native_decide|^axiom" B C
    1002 RBM3D/Graph/BATermHoldsB.lean
     126 RBM3D/Graph/BALWOut.lean
grep exit 1
$ lake build RBM3D.Graph.BATermHoldsB RBM3D.Graph.BALWOut 2>&1 | tail -1; ... | grep -c "BATermHoldsB.lean\|BALWOut.lean"
Build completed successfully (4146 jobs).
0
$ lake build   (full library at HEAD with the import lines and the registry edits; started/ended by date -u)
Tue Oct 13 09:12:50 UTC 2026|Tue Oct 13 09:14:00 UTC 2026|
Build completed successfully (4365 jobs).
exit=0
6384:info: RBM3D.lean:597:0: axiom audit: 14822 theorems, 4587 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
error lines: 0; lines of the log naming BALWterm: 0
$ lake env lean axall.lean  (#print axioms)
'RBM.BA.BALWtermExpS' [propext, Classical.choice, Quot.sound]
'RBM.BA.baLWtermExpS_holds' [propext, Classical.choice, Quot.sound]
'RBM.BA.baLWtermExp_holds' [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep2_closed' [propext, Classical.choice, Quot.sound]
'RBM.BA.baLWCutExpTw_holds' [propext, Classical.choice, Quot.sound]
'RBM.BA.baLWtermEXPTw_holds' [propext, Classical.choice, Quot.sound]
$ targets by script: awk from def BALWtermExpS to the blank line; grep -n of the theorem lines
821: def BALWtermExpS (d : ℕ) : Prop :=
822:   3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
823:     ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
824:       ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
825:         ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExpgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ℓ →
826:           ∀ D : ℝ, 0 < D →
827:             PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
828:                 sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
829:               (fun n p ω => ‖LWEg (baFMz sz z) n (t n) p.1.1 p.1.2 ω‖)
830:               (fun n p _ => ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
831:                 ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
832:                   ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ)))
838:theorem baLWtermExpS_holds : ∀ d : ℕ, BALWtermExpS d := by
865:theorem baLWtermExp_holds : ∀ d : ℕ, BALWtermExp d := by
879:theorem baStep2_closed : ∀ d : ℕ, BAStep2 d := fun d => baStep2_holds d (baLWterm_holds d) (baLWtermExp_holds d)
48:theorem baLWCutExpTw_holds : ∀ d : ℕ, BALWCutExpTw d :=
54:theorem baLWtermEXPTw_holds : ∀ d : ℕ, BALWtermEXPTw d :=
$ the check texts and the scratch copy of the check file (imports BATermHolds, BATermHoldsB, BALWOut; not committed)
191:def T2494_TermClosed : Prop := ∀ d : ℕ, BALWterm d
195:def T2494_TermExpClosed : Prop := ∀ d : ℕ, BALWtermExp d
199:def T2494_Step2Closed : Prop := ∀ d : ℕ, BAStep2 d
202:def T2494_CutClosed : Prop := ∀ d : ℕ, BALWCutExpTw d
206:def T2494_EXPClosed : Prop := ∀ d : ℕ, BALWtermEXPTw d
259:example : T2494_TermClosed := baLWterm_holds
260:example : T2494_TermExpClosed := baLWtermExp_holds
261:example : T2494_Step2Closed := baStep2_closed
262:example : T2494_CutClosed := baLWCutExpTw_holds
263:example : T2494_EXPClosed := baLWtermEXPTw_holds
lake env lean check_rowb.lean: exit=0, error lines: 0
$ sed -n (instance of target 4); grep -n of the other instances
B:960-970
example (hI : STInitialGT2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (1 / 10) Ψ0)
    (hL : LWLoopExpgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) BATermHoldsB_ℓ0) :
    PrecL sz0 μ0 (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 < 1 - (1 / 2 : ℝ)})
      (fun n p ω => ‖LWEg (baFMz sz0 zSeq) n (1 / 2 : ℝ) p.1.1 p.1.2 ω‖)
      (fun n p _ => ((baFMz sz0 zSeq).eta n (1 / 2 : ℝ))⁻¹ * (sz0.Bctl n (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) *
        ((((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * tailW 3 (sz0.L n) (sz0.lam n) (1 / 2 : ℝ) (BATermHoldsB_ℓ0 n) ((sz0.W n : ℕ) : ℝ) 5
          ((zdistInf 3 (sz0.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ))) :=
  baLWtermExpS_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) Ψ0 BATermHoldsB_ℓ0
    ⟨by norm_num, Ψ0_window, hI, fun n => zero_le_one.trans (BATermHoldsB_ℓ0_ge n), BATermHoldsB_ℓ0_le, hL⟩ 5 (by norm_num)
BATermHoldsB.lean:945:example : ∀ n, Nonempty {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
BATermHoldsB.lean:952:example : ∀ n, ∀ t : ℝ, t ≤ BAflowT0 sz0 zSeq n → sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 < 1 - t 
BATermHoldsB.lean:960:example (hI : STInitialGT2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (1 / 10) Ψ0)
BATermHoldsB.lean:973:example (hI : STInitialGT2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (1 / 10) Ψ0)
BATermHoldsB.lean:980:  baLWtermExp_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (
BATermHoldsB.lean:986:example : ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
BATermHoldsB.lean:992:  obtain ⟨Cd, hCd, 𝔠d, h𝔠d, h𝔠d1, h⟩ := baStep2_closed 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm
BALWOut.lean:87:example : ∀ n, Nonempty {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
BALWOut.lean:94:example (hE : STLocalEntrygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
BALWOut.lean:102:  baLWtermEXPTw_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 /
BALWOut.lean:109:example (hE : STLocalEntrygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
BALWOut.lean:117:  baLWCutExpTw_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 
$ grep -nE "sz\.lam|withLam|gK" B | awk (statement lines 821-832 of the def BALWtermExpS); theorem statements have the binder d only
825:        ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExpgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ℓ →
827:            PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
828:                sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
831:                ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
hits in all of B: 54; in C: 1; gK: RBM3D/Graph/BATermHoldsB.lean:0 RBM3D/Graph/BALWOut.lean:0 
$ grep -nE "LWAssmgL|LWAssmExpgL|BAExp14bS2|BATwist|BALWCutExpTw" B C  (code lines only)
RBM3D/Graph/BATermHoldsB.lean:399:  (ht1 : ∀ n, t n ≤ BAflowT0 sz z n) (hA : LWAssmExpgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ 
RBM3D/Graph/BATermHoldsB.lean:825:        ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExpgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ℓ →
RBM3D/Graph/BALWOut.lean:97:    (hT2 : BATwistLoopLaw (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) :
RBM3D/Graph/BALWOut.lean:112:    (hT2 : BATwistLoopLaw (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) :
$ grep -cE "BAAnpAuxG|BAShapePath|STGridRepNgL" B C; grep -cwE "mE|STGM|STKloop|etaT|STflowE|lwS" B C
RBM3D/Graph/BATermHoldsB.lean:0 RBM3D/Graph/BALWOut.lean:0 
RBM3D/Graph/BATermHoldsB.lean:0 RBM3D/Graph/BALWOut.lean:0 
$ git diff --stat main...t/T2494b; importers of the new modules
 RBM3D.lean                    |    2 +
 RBM3D/Graph/BALWOut.lean      |  126 ++++++
 RBM3D/Graph/BATermHoldsB.lean | 1002 +++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean        |   13 +-
 4 files changed, 1135 insertions(+), 8 deletions(-)
RBM3D.lean:593:import RBM3D.Graph.BATermHoldsB
RBM3D.lean:594:import RBM3D.Graph.BALWOut
$ name-clash: git grep -w -E "BALWtermExpS|baLWtermExpS_holds|baLWtermExp_holds|baStep2_closed|baLWCutExpTw_holds|baLWtermEXPTw_holds" <ref> -- RBM3D RBM3D.lean   (files with a hit; stems BATermHoldsB_|BALWOut_ : files)
main 035c4b84: [RBM3D/Graph/BAExp14a2.lean:1 RBM3D/Graph/BATermHolds.lean:1 ] stems: 0 files
t/T2489b a4e272dc: [RBM3D/Graph/BAExp14a2.lean:1 ] stems: 0 files
t/T2491 ae93f0a2: [] stems: 0 files
t/T2491b 2cd1f7db: [RBM3D/Graph/BAExp14a2.lean:1 ] stems: 0 files
t/T2491c 5545bcf1: [RBM3D/Graph/BAExp14a2.lean:1 RBM3D/Graph/BATermHolds.lean:1 ] stems: 0 files
t/T2492 9f0a3641: [RBM3D/Graph/BAExp14a2.lean:1 ] stems: 0 files
t/T2493 b430f3c2: [RBM3D/Graph/BAExp14a2.lean:1 ] stems: 0 files
t/T2495 add74cd9: [RBM3D/Graph/BAExp14a2.lean:1 ] stems: 0 files
t/T2496 4e5e3b82: [RBM3D/Graph/BAExp14a2.lean:1 ] stems: 0 files
$ declarations of those names on the sibling refs (theorem|def|abbrev lines): 0 lines (own branch: 6)
$ RBM1D/RBM2D ports: grep -rlE "LWterm|lwterm|LWcut|lwReduce|LWEg|sfT" ../RBM1D ../RBM2D --include=*.lean | wc -l
0
$ git grep -n -w BALWtermEXP -- RBM3D (five-premise pin: readers/producers); registry lines for the L6/Step 2 pins
RBM3D/BA/LWPinsBA.lean:49:abbrev BALWtermEXP : ℕ → Prop := baPin LWtermEXPG
RBM3D/BA/LWPinsBA.lean:102:example (h : BALWtermEXP 3) (hE : STLocalEntrygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 
       0
```

Closing conditions (T2387 §8 (6), L40-C1), this row (file:line on `t/T2494b`):
- (i) `BALWterm`: `baLWterm_holds` `BATermHolds.lean:706` (row a, merged); `BALWtermExp`: `baLWtermExp_holds` `BATermHoldsB.lean:865`. (ii) `BALWtermEXPTw`: `baLWtermEXPTw_holds` `BALWOut.lean:54`.
- (iii) Instances at `d = 3`: (a) `BATermHolds.lean:883` (row a); (b) `BATermHoldsB.lean:960` (target 4), `:973` (target 5); the regime `1 - t ≤ λ²/L²` has no instance (n/a: its index set is empty at `sz0`, `zSeq` for every `t ≤ BAflowT0`, compiled at `BATermHoldsB.lean:952` from `BAflowT0 ≤ 25/36`; at `t ≡ 1/2` also `BATermHolds.lean` §4); (c) `BALWOut.lean:94` (7 (b)), `:109` (7 (a)); (d) `BATermHoldsB.lean:986`.
- (iv) `BAGGGamma`: `baGGGamma_holds` `BAGGExp.lean:358` (merged, not edited). (v) Owed-pin lines: `BALWterm`, `BALWtermExp` and the T2487 header comment deleted, owner texts of `LWtermG`, `LWtermExpG`, `STLocalEntryUgL`, `STAvgUgL`, `STStep2ConclgL` changed (`Test/Axioms.lean`, 13 lines in the diff stat above); the full build passes the audit and the log names neither pin.
- (vi) Carrier forms unchanged: the five `example : T2494_X := name` above; `baStep2_closed` `BATermHoldsB.lean:879`. (vii) `BAAnpAuxG` is concluded by `baAnpAuxG_holds` `BAAnpLift.lean:229` (T2488), the path binder by `baLWMomentOfAnp_closed` `BAMomentExpGen.lean:189` (T2483); neither name occurs in B or C (count 0 above). (viii) T2490 target 5: `BALWOut.lean:48`, `:54`.
- (ix) The five-premise `BALWtermEXP` (`LWPinsBA.lean:49`) has no producer and no reader (its definition and the instance `LWPinsBA.lean:102` only) and no registry line: recorded, not edited (T2490a).

Census (kinds: public = used by name; `open private` = `BATermHoldsB.lean:65-66`, `:895-896`; stem copy = text adapted into B with the stem `BATermHoldsB_`):
- Markov (`BATermHoldsB_fT` B:500): public `LWTermHolds_prec_of_moments` LWTermHolds:97, `baLWMomentExp_closed` BAAnpLift:258, `BAMomentExp_integrable` BAMomentExpGenB:263, `LWfgD_univ` BAMomentExpGen:91, `BAExp14a_det_iff` BAExp14a:58; stem copy of `LWTermHolds_fT` :1487 and `BATermHolds_fB` BATermHolds:458.
- `(eq:directG2)` (`BATermHoldsB_GM_T` B:405): public `baGbyZeta_holds` BAAuxGraph2B:623, `baZetaExpClaim_holds` BAZetaExp:325; replaces `LWTermHolds_Gij_T` :1047 (its lemmas `LWTermHolds_xiSq_le` :762 and `LWTermHolds_sfT_shift` :841 are not read).
- `(GavLGEX)` (`BATermHoldsB_avg` B:432): public `baGbEXPav_holds` GbEXPav:24, `LWWindow_max_Bctl` LWPsi:344, `BAExp14d_Bctl_small` BAExp14dB:74 (in the place of `lwN_Bctl_le`), `lwN_prec_mono` LWTermExpN:42, `BAMomentGen_prec_of_whp`/`_whp_of_prec` BAMomentGen:165/179; stem copy of `LWTermHolds_avg_T` :1182. Window `ε₁` (`BATermHoldsB_eps` B:310): stem copy of the computation in `baLWtermExpN_holds` BATermHolds:758.
- `M`-part: `BATermHoldsB_Mpart` B:285 (stem copy of `BATermHolds_Mpart` BATermHolds:556 and `BAMomentGen_decay` BAMomentGen:651, without their `LWAssmgL` binder) from public `BAMomentGen_consts` BAMomentGen:364, `BAflow_lam0_window` GreenSchur:72, `ba_G_data` GreenLDE:55; `BATermHoldsB_sfMb` B:206 (new; open private `BATermHolds_poly_exp` BATermHolds:402).
- Core (`BATermHoldsB_core` B:564, stem copy of `LWTermHolds_reduceT_core` :1270): open private `BATermHolds_LWE_le` :213, `BATermHolds_W_tendsto` :432, `BATermHolds_zdistInf_le` :749, `LWTermHolds_arithT` :934, `_tail_cmp` :917, `_sfT_sq_le` :885, `_sfT_zero_sq` :904, `_A_ge` :908; public `BAflow_real` GreenSchur:59, `BAExp14a_eta_pos` BAExp14a:1266, `BAExp14c_eta_le_one` BAExp14c:712; arithmetic `BATermHoldsB_arithT` B:73 (new M-part; calls `LWTermHolds_arithT`).
- B:838, B:865, B:879: stem copies of `LWTermHolds_concT` :1551 and `lwtermExp_holds` :1604; public `baLWtermExpN_holds` BATermHolds:758, `baLWterm_holds` :706, `baStep2_holds` Step2CloseBA:181. C:48, C:54: public `baLWCutExpTw_of_S2` BAExp14a2:272, `baLWtermEXPTw_of_S2` :326, `baExp14bS2_holds` BAExp14b2B:1064 (read at the merged type only), `baTwistAvgProd_holds` TwistAvgB:451 (instances, C:104, C:119). Instances (B:895-896): open private `Ψ0`, `Ψ0_window` LWPinsBA:72-73, `FlowPins_zS_add_mS_im`, `FlowPins_wI_im` FlowPins:1127, :1117.

UBA-C1 (§273 (1)): not triggered; `gK` count 0; no comparison other than the pin vocabulary. U5S-C3: the six public statements above have the binder `d : ℕ` only: family-premise table empty; eventual BA facts enter per index under `∀ᶠ n` (B:294 `BAflow_lam0_window`, B:601 `Admissible.WO`). TN-C4: `STGridRepNgL` count 0.
| targets | `sz.lam` read | coupling `g₀` read | crossing |
|---|---|---|---|
| 4-5 | pin vocabulary (`LWAssmExpgL` window, `tailW`, `sfT`; B:828, B:831); `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹` from `WO` (B:601-613) | `BAflow_lam0_window` (B:294) and the producers; constants of `BAMomentGen_consts` in `(d, 𝔡, κ)` | none |
| 6 | none | inside `baStep2_holds` | none |
| 7 | the pins' `U` (`λ²/L^d ≤ 1 - t`) | inside `baFMz` | none |
| 8 | `sz0` | `zSeq` | none |
L40-C2: the coupling range read is `0 < lam n ≤ 𝔡⁻¹` eventually (`T2494-prove.md:64`), not wider than `T2483b-prove.md:61`.
Hypotheses of the instances (every other hypothesis is discharged): B:960, B:973: `hI : STInitialGT2gL` (registry `Test/Axioms.lean:190`), `hL : LWLoopExpgL` (no registry line; the loop part of `LWAssmExpgL`, `Chain/LWGen.lean:64`). B:986: the binders of the stated conclusion `STLKgL` (:135), `STDecaygL` (:217), `STConStInd` (:268), `STStep1LoopgL` (:236), `STStep1WeakgL` (:146); `BALWterm 3`, `BALWtermExp 3` are not hypotheses. C:94, C:109: `STLocalEntrygL` (:144), `LWAvgLawgL` (no registry line), `STLmaxgL` (:133), `STLKgL` (:135), `STDecaygL` (:217), `BATwistLoopLaw` (:193); TL1 `BATwistAvgLaw` (:192) is produced by `baTwistAvgProd_holds 3` (C:104, C:119). All registry lines are `Test/Axioms.lean` lines on `t/T2494b`.

Narrative.
1. Scope. Row b of the pre-signed split A | B + C: file B (targets 4-6, 8 (b), (d)), file C (target 7, 8 (c)), target 9 and the two root import lines. File A (targets 1-3) is merged and not edited; no reserve file, no third row. No step of `7_8:15-91` needed a producer that is not merged, and no new pin or hypothesis outside C1 (S1 not triggered).
2. Delivered. `baLWtermExpS_holds` B:838 (statement def `BALWtermExpS` B:821): every `D > 0`, through `D' = max (D, 2d + 1)`. `baLWtermExp_holds` B:865: the union with `baLWtermExpN_holds` of file A; its type is the merged pin `BALWtermExp`. `baStep2_closed` B:879: one line from `baStep2_holds`. `baLWCutExpTw_holds` C:48, `baLWtermEXPTw_holds` C:54: one line each from the merged `…_of_S2` and `baExp14bS2_holds`; `BAExp14bS2` is not a binder of any public result.
3. Route of target 4 (`7_8:20-58`; `B:286-288` says "analogously"). `(eq:directG2)`: `baGbyZeta_holds` at `R = 0`, `ρ_n = log N √(log N)`, then `baZetaExpClaim_holds`, composed by `StochDomAt.trans` (B:405); no `ξ²` lemma and no shift lemma of the band. `(GavLGEX)`: `baGbEXPav_holds` at `Ψ_t = max (W^{-d/2}, Bctl^{1/2})`, with `Bctl ≤ W^{-2ε₁}` from `BAExp14d_Bctl_small` (B:310, B:432). Markov: `baLWMomentExp_closed` (B:500). The reduction (B:564) calls `BATermHolds_LWE_le` of file A.
4. The `M`-part on the `T` side. At BA the closing edge is `G_{yx} = GM_{yx} + M_{yx}`; `M_{xy} = 0` off equal offsets and `‖M_{xy}‖ ≤ C' e^{-c r}` (B:285), and exactly a `W^{-d}` fraction of the pairs of two blocks has equal offsets (file A). The new inequality is `𝖳_t(0) e^{-c r} ≤ E 𝖳_t(r ∧ ℓ)` (B:206, `E` in `(d, c)`, `ℓ_t ≥ 1`), which turns the `M`-terms of the pathwise bound into multiples of `u (s² + W^{-d} w)` in B:73.
5. Instances. Target 4 (B:960) and target 5 (B:973) at `d = 3`, `sz0`, `zSeq`, `flow_sz0`, `t ≡ 1/2 ≤ BAflowT0`, `ε₀ = 1/10`, `Ψ_n = W_n^{-1/2}`, `ℓ_n = ℓ_t = ellT` (`≥ 1` and `≤ (log W_n)^{10} ℓ_t`, so the window is not collapsed), `D = 5 < 2d + 1`; the index set of the regime of target 4 is nonempty at every `n` (B:945). The regime `1 - t ≤ λ²/L²` is empty at this data for every admissible `t` (B:952), so target 5 is exercised through the first regime. Target 6 (B:986) at `s ≡ 1/10 < t ≡ 1/2`; target 7 (C:94, C:109) with TL1 from `baTwistAvgProd_holds 3`.
6. Registry and root: `Test/Axioms.lean` edits as in (v); `RBM3D.lean` carries `import RBM3D.Graph.BATermHoldsB` and `import RBM3D.Graph.BALWOut` after the last import (lines 593-594). The full `lake build` at HEAD (started and ended by `date -u` above): 4365 jobs, 0 error lines, `0 axioms` in the audit line.
7. Hygiene: the public results have the binder `d : ℕ` only; the only pin hypothesis among the binders of any lemma is `hA : LWAssmExpgL` of the private lemmas (B:399), besides the instance hypotheses; every helper is private; no `sorry`, no new `inductive`, no band object in a statement, no `gK`.
8. Ports: none from RBM1D/RBM2D (the count above is 0); every source is an RBM3D file listed in the census.

## (c) Verified Mathlib names used (128 names: the identifiers of the two files, resolved by `Lean.resolveGlobalName` in the environment of the two modules; script in the scratchpad; names verified absent: none)
Real: Real.abs_le_sqrt Real.exp Real.exp_add Real.exp_le_exp Real.exp_one_lt_d9 Real.exp_pos Real.le_log_iff_exp_le Real.log Real.log_le_log Real.log_nonneg Real.mul_self_sqrt Real.one_le_rpow Real.rpow_add Real.rpow_le_one_of_one_le_of_nonpos Real.rpow_le_rpow_of_exponent_le Real.rpow_mul Real.rpow_natCast Real.rpow_neg Real.rpow_neg_one Real.rpow_nonneg Real.rpow_one Real.rpow_pos_of_pos Real.rpow_two Real.sq_sqrt Real.sqrt Real.sqrt_eq_rpow Real.sqrt_le_iff Real.sqrt_le_one Real.sqrt_le_sqrt Real.sqrt_mul Real.sqrt_nonneg Real.sqrt_one Real.sqrt_pos Real.sqrt_sq Real.tendsto_log_atTop
Nat/Fintype/Filter/Finset/core: Bool.false Bool.true Filter.atTop Filter.eventually_ge_atTop Filter.Eventually.of_forall Finset.sup'_le Finset.univ Fintype.card_prod Fintype.card_subtype_le Nat.cast_le Nat.cast_nonneg Nat.cast_pos Nat.cast_zero Nat.le_ceil Nat.le_mul_of_pos_right Nat.le_self_pow Nat.one_le_cast Nat.pow_le_pow_left Or.inl Or.inr
ordered-field and algebra: add_nonneg add_zero div_eq_mul_inv div_le_iff₀ div_le_one div_le_self dvd_mul_right ge_iff_le inv_anti₀ inv_le_one_of_one_le₀ inv_mul_cancel₀ inv_nonneg inv_one inv_pos le_abs_self le_add_of_nonneg_right le_div_iff₀ le_max_left le_max_right le_min le_mul_of_one_le_left le_mul_of_one_le_right le_of_mul_le_mul_left le_rfl le_total le_trans lt_max_of_lt_left lt_min lt_of_lt_of_le max_eq_left max_eq_right max_le max_le_max min_eq_left min_le_left min_le_right mul_comm mul_div_cancel₀ mul_le_mul mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right mul_le_of_le_one_left mul_le_of_le_one_right mul_max_of_nonneg mul_nonneg mul_one mul_one_div_cancel mul_pos mul_pow mul_self_nonneg MulZeroClass.mul_zero norm_add_le norm_nonneg not_lt one_div one_le_inv_iff₀ one_le_pow₀ one_mul one_pos one_pow pow_add_pow_le pow_le_one_iff_of_nonneg pow_le_pow_left₀ pow_le_pow_right₀ sq sq_nonneg sub_nonneg sub_zero tendsto_rpow_atTop two_ne_zero zero_add zero_le_one zero_le_two

## (d) Open issues and paper-delta candidates
- `T2494c` (paper-delta candidate): `(eq:directG2)` and the cut average at BA read `|G_{yx}| ≺ δ_{xy} + 𝖳_t(|a-b| ∧ ℓ) + W^{-D} + |M_{yx}|` in the regime `1 - t > λ²/L²`; the paper (`B_graphical_lemmas.tex:286-288`, "analogously") gives no argument for the `M_{yx}` term, which Lean closes by the offset support and the decay of `M` with the weight `W^{-d}` and `𝖳_t(0) e^{-c r} ≤ E 𝖳_t(r ∧ ℓ)` (`BATermHoldsB_sfMb`). Companion of `T2494a` (row a, regime `1 - t ≤ λ²/L²`).
- Inherited, not new: the regime split of `lem: EWGn2_N` and the B class (band candidate `T2342a`, `Graph/LWTermExpN.lean:413`); the restriction `D ≥ 2d + 1` of the cross term and its branch through `max (D, 2d + 1)` (band candidate `T2375c`).
- The regime `1 - t ≤ λ²/L²` has no nonempty instance at the merged flow data (compiled emptiness for every admissible `t`: B:952); target 5 is exercised through the other regime.
- Observation, `Test/Axioms.lean:197` (`STGdecayWgL`, a line of T2495 per the ticket, not edited): its note still reads "inputs `BALWterm`/`BALWtermExp` (BA-L6)"; `baStep2_closed` makes it stale.
- `main` moved after the merge of `main` into this branch (035c4b84 in the evidence above; the Lean change since 1843bd31 is T2491 U3s2b: `RBM3D.lean` +2 import lines and two new leaf files): the merge needs the union of the import lines of `RBM3D.lean`; `Test/Axioms.lean` has no change on `main` since 1843bd31 (`git diff --stat 1843bd31 main -- RBM3D RBM3D.lean` lists three files, none of them `Test/Axioms.lean`).
- After this merge the stage-L closing REQ follows (ticket, "After merge"). Consumers named in the ticket and in `BAExp14a2.lean:325`: V and T2495 read `baStep2_closed`; V1-BA reads `baLWtermEXPTw_holds`.
