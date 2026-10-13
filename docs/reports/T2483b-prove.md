Prover model: claude-sonnet-5-5

## (a) Math preflight
Section (a) of this ticket is `docs/reports/T2483-prove.md` (a) and (a′) (verdict PASS for targets 1-10, written for both halves); this stage (L3d2b-2: targets 6-10, file `BAMomentExpGenB`) wrote no section (a).
Its exponent table (rows 3-12) is the one this part uses; the verdict-table lines for targets 6-10 stand.

### (a′) Preflight corrections — Tue Oct 13 04:11:30 UTC 2026
No verdict changes. (1) (a)(ii) names `ε₀ = 1/10`, `ℓ = 1` as instance data; the instances of this part use the merged band data `ε₀ = 1/20`, `Ψ_n = W_n^{-1}` (`Ψ0`, `window0`), `ℓ_n = ℓ_t` (`ℓT`, `1 ≤ ℓ_n ≤ (log W)^{10} ℓ_t`),
`t ≡ 1/2 ≤ BAflowT0`, `p = 2`, `d = 3`, `sz0`, `zSeq`, `flow_sz0` (`κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`; `n = 0`: `L = 4`, `W = 32`). (2) (a) row 10: the window of `LWPhiB` is `ε₁ = min(ε₀, d c₀/4)`, `c₀` of `BAExp14d_Bctl_small`
(`Bctl ≤ 2 N^{-c₀}`; the factor 2 is absorbed by `d c₀/4` in place of the band's `d c/2`). (3) (a) row 7 is realized as `ρ = (2K+1)(log W)^{3/2}`, `R = K (log W)^{3/2}`, `ρ - 2R = (log W)^{3/2}` (`√ρ ≤ τ log N` from `lwMomentExp_rad` at `K + 1/2`).

## (b) Script output — Tue Oct 13 04:11:30 UTC 2026
**Delivered: L3d2b-2 = `RBM3D/Graph/BAMomentExpGenB.lean` (1344 lines): targets 6-9 and instance (i) of target 10; instances (ii), (iii) of target 10 are in part A (merged).** One file; no reserve file `BAMomentExpGenC` (1,800-line rule not reached).
Branch `t/T2483b` = merge of `main` (merge commit `5c4c3362`, L3d2b-1 `772b1ca1` included) + 8 commits; `RBM3D.lean` and `Test/Axioms.lean` untouched (the root import line is the hub's at merge, as for part A).
**Start decision (L3d1):** `git grep -nE "(theorem|lemma) .*BAAnpAuxG"` finds 0 hits on the branch base `5c4c3362` and 0 on `main` `94e626a1`: L3d1 is not merged, target 9 stays as pinned, `T2483_MomentExpClosed` is not proved.

**Line counts vs the stop line (2,000 per file, binding); the split is the pre-signed one (this file = targets 6-10):**
```
$ for h in $(git log --reverse --format=%h 5c4c3362..HEAD); do …; git show $h:RBM3D/Graph/BAMomentExpGenB.lean | wc -l; done
68efcc8e Oct 13 02:48:49 UTC lines=234 T2483b: BAMomentExpGenB sections 1-2 (context LWAssmgL for the B class
dedc09bd Oct 13 02:52:14 UTC lines=428 T2483b: BAMomentExpGenB section 3 (weighted expansion, integrability, 
5ed71f0a Oct 13 02:54:16 UTC lines=625 T2483b: BAMomentExpGenB section 4a (control R, errors, scale-mole outp
b9971fac Oct 13 03:17:32 UTC lines=946 T2483b: BAMomentExpGenB section 4b (outputs with M_x != M_y: rooted G3
0927d03e Oct 13 03:39:31 UTC lines=1128 T2483b: BAMomentExpGenB section 5 (BAMomentExpOn, pin_gen, far and nea
fd0ab8a3 Oct 13 03:43:12 UTC lines=1209 T2483b: BAMomentExpGenB section 6 (assembly baMomentExp_of_parts, baLW
0825fece Oct 13 03:46:35 UTC lines=1340 T2483b: BAMomentExpGenB section 7 (compiled nonempty instances of targ
eead4288 Oct 13 03:59:00 UTC lines=1344 T2483b: BAMomentExpGenB final (docstring, ports line, heartbeat commen
```

**Build, check file, full-library audit with this module imported** (scratch file `import RBM3D`, `import RBM3D.Graph.BAMomentExpGenB`, `#assert_rbm_axioms`; `Test/Axioms.lean` unchanged; the full `lake build` is the hub's merge step):
```
$ lake build RBM3D.Graph.BAMomentExpGen RBM3D.Graph.BAMomentExpGenB | tail -2 ; grep -c "BAMomentExpGenB.lean" build.log   # fresh build of the final source
✔ [4069/4069] Built RBM3D.Graph.BAMomentExpGenB (53s)
Build completed successfully (4069 jobs).
warnings of this file: 0
$ lake env lean docs/tickets/checks/T2483-check.lean ; echo exit   ->  check exit=0
$ lake env lean full_ax.lean | head -2 ; grep -c error   ->  error lines: 0
axiom audit: 14377 theorems, 4529 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: what the paper …
$ #print axioms of the 9 public theorems of the file ; sed … | sort | uniq -c
   9 [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|axiom |^(structure|inductive|class) " RBM3D/Graph/BAMomentExpGenB.lean ; echo exit=$?   ->  exit=1
```

**L40-C2 (case (b)).** Statement: `BAMomentExpOn`/`BAMomExpNoExp` put `∀ᶠ n` last (inside `PrecL`, after `p, 𝔠, sz, z, t, ε₀, Ψ, ℓ, D`); the constants `(C, c, Kd)` (`BAMomentGen_consts d hd 𝔡⁻¹ κ` via `BAMomentGen_decay`), `(K₀, K₁, Kd, Cg, cg)`
(`baGtoAGTRooted_holds d hd 𝔡⁻¹ κ`), `c₀` (`BAExp14d_Bctl_small`) and `K_c` (sum of the list sizes of `ba_localregularXP`) are fixed before every `filter_upwards`; the coupling `g₀ = BAflowLam0 sz z n` enters only as `0 < g₀ ≤ 𝔡⁻¹` (`BAflow_lam0_window`, eventual):
```
$ grep -nE "obtain .*(baGtoAGTRooted_holds d hd|BAMomentGen_decay hd|BAExp14d_Bctl_small d)|filter_upwards \[(hdec,|BAMomentGen_Psi_facts hd|BAExp14a_eventual|hB t)|BAflow_lam0_window" RBM3D/Graph/BAMomentExpGenB.lean | cut -c1-118
85:  obtain ⟨c₀, hc₀, hB⟩ := BAExp14d_Bctl_small d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow
105:    filter_upwards [hB t ht0 ht1, hbig] with n hn hb2
485:  obtain ⟨C, c, Kd, hC, hc, hKd, hdec⟩ := BAMomentGen_decay hd hκ hε h𝔡 hflow ht0 ht1 hassm
488:  filter_upwards [hdec, BAMomentGen_Psi_facts hd hκ hε h𝔡 hflow ht0 ht1 hassm (τ₁ := 𝔠 * ε₁ / 4) (by positivity) l
536:  obtain ⟨C, c, Kd, hC, hc, hKd, hdec⟩ := BAMomentGen_decay hd hκ hε h𝔡 hflow ht0 ht1 hassm
538:  filter_upwards [hdec, BAMomentGen_Psi_facts hd hκ hε h𝔡 hflow ht0 ht1 hassm (τ₁ := 𝔠 * ε₁ / 4) (by positivity) l
591:  obtain ⟨C, c, Kd, hC, hc, hKd, hdec⟩ := BAMomentGen_decay hd hκ hε h𝔡 hflow ht0 ht1 hassm
595:  filter_upwards [hdec, BAExp14a_eventual_scalars hκ hε h𝔡 hflow ht0 ht1,
703:  obtain ⟨K₀, K₁, Kd, Cg, cg, hK₀, hK₁, hKd, hCg, hcg, hGT⟩ := baGtoAGTRooted_holds d hd 𝔡⁻¹ κ (inv_pos.2 h𝔡) hκ
720:  filter_upwards [BAMomentGen_Psi_facts hd hκ hε h𝔡 hflow ht0 ht1 hassm hτ₁.le ((min_le_left _ _).trans (min_le_ri
726:    BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow]
```
Limit check over L5's range (every `𝔡, κ > 0`; `BAct_rate_pos`; the sup of every threshold is at `Λ = 𝔡⁻¹`) and the O4 numbers (script `c2.py` of the 1a, copied unchanged and rerun; the Lean thresholds are eventual, no instance uses them):
```
grid points 168; rate<=0 or p5rate<=0 at 0; rate(Lam) > rate(g0) for some g0 <= Lam at 0
   g=Lam   eta      Im m         rate       p5rate lam0_O4(rate) lam0_O4(p5rate)
 0.01562   0.1  0.950589   4.7529e-01   8.2740e-10    4.4341e+02      1.4607e+20
 0.01562   1.0  0.617784   3.0889e-01   5.4554e-13    1.0492e+03      3.3601e+26
 1.00000   0.1  0.554668   4.5186e-02   6.5009e-23    4.8980e+04      2.3662e+46
 1.00000   1.0  0.354845   2.9142e-02   3.4641e-26    1.1776e+05      8.3331e+52
10.00000   0.1  0.511681   4.2549e-03   1.9048e-32    5.5235e+06      2.7560e+65
10.00000   1.0  0.251349   2.0924e-03   1.0836e-37    2.2841e+07      8.5167e+75
lwTail32 threshold ln W >= (2A/(frakc*Krad*c))^2, c = p5rate (eta = 0.1), A = a+b = 6+10 = 16, Krad = 1/K_c (K_c = 1 here; scales as K_c^2):
   g= 0.01562: frakc = 1: 1.496e+21 ; frakc = 1/6 (flow_sz0): 5.385e+22
   g= 1.00000: frakc = 1: 2.423e+47 ; frakc = 1/6 (flow_sz0): 8.723e+48
   g=10.00000: frakc = 1: 2.822e+66 ; frakc = 1/6 (flow_sz0): 1.016e+68
```
Stop rule L40-C2 not triggered: no threshold depends on a sequence element's coupling, on `t`, `E` or `n` beyond `(d, 𝔡⁻¹, κ)` and the fixed exponents.

**L4-C4 (b)** (`𝓜_x = 𝓜_y`, every `x ~ y` among them): `BAMomentExp_pin_gen` splits the outputs by `o.Q.g.mol (inl (ext 0)) = o.Q.g.mol (inl (ext 1))`; the equal case is `BAMomentExpGenB_prec_scale`
(weighted scale-mole tail `BAMomentExp_scalemole` at radius `(K/K_c)(log W)^{3/2}`, hypothesis `inl (ext 1) ∈ mol (inl (ext 0))` only; `BALocReg1_mol_of_atom` is not needed); the other case needs `mol ≠ mol` and goes to the shadow (`BAAtom_shadow_molOf_eq_iff`, `BAAtom_mol_eq_of_mem`):
```
$ grep -nE "by_cases hmol|BAMomentExpGenB_prec_(scale|anp) hd|BAAtom_mol_eq_of_mem|hmol\]; exact BAMomentGen_mem_mol_self" RBM3D/Graph/BAMomentExpGenB.lean | cut -c1-130
1051:      by_cases hmol : o.Q.g.mol (Sum.inl (o.Q.ext 0)) = o.Q.g.mol (Sum.inl (o.Q.ext 1))
1052:      · refine BAMomentExpGenB_prec_scale hd hκ hε h𝔡 hflow ht0 ht1 hassm p hD (Krad := K / Kc) (div_pos hK hKc0)
1053:          (V := V) (fun n v => v.1) dom o hQ (by rw [hmol]; exact BAMomentGen_mem_mol_self _ _) ?_
1072:          exact (BAAtom_mol_eq_of_mem o.Q.g ((BAAtom_shadow_molOf_eq_iff o.Q.g _ _).1 h'')).symm
1073:        exact BAMomentExpGenB_prec_anp hd hκ hε h𝔡 hflow ht0 ht1 hassm hAss hp0 hK hKc0 hD (V := V) (fun n v => v.1) dom o
```

**Section map as written** (band → here; `LWMomentExp` = `Graph/LWMomentExp.lean`, `LWMomentExpA` = `Graph/LWMomentExpA.lean`):
| band | here |
|---|---|
| `LWMomentExpA` §1 `:46-65`, §4 `:328-404` | §2: `BAMomExpNoExp`, `BAMomExpNoExpOfMoment`, `baMomExpNoExp_of_moment`; `LWMomentExpA` §2-§3 `:67-326` (`lwMEA_prec_mono`, `_phiB_sq_le`, `_loss`, `_phi_*`) imported by `open private` |
| `LWMomentExpA` `lwMEA_assm` `:127`, `LWMomentExp` §5 `:481-541` | §1: `BAMomentExpGenB_assm` (one BA copy for both) |
| `LWMomentExp` §1 `:85-107`, §2 `:108-239` | §5 `BAMomentExpOn`, `BAMomExpFarPin`, `BAMomExpNearPin`; §3 `BAMomentExp_integrable`; §6 `BAMomentExpOfParts`, `baMomentExp_of_parts` (`lwMomentExp_comb` by `open private`) |
| `LWMomentExp` §4 `:375-460`, §10 `:1289` | §3 `BAMomentExp_expand` (weight and roots: part A), `BAMomentExp_LWfgD_zero` (`lwMomentExp_LWfD_zero`) |
| `LWMomentExp` §6-§8 `:543-801` | imported unchanged (`lwMomentExp_PinN`, `_pinN_far/near`, `_valOn_floor/_smul`, `_rad`, `_arith`) |
| `LWMomentExp` §9 `:802-1285` | §4: `BAMomentExpGenB_R`, `_prec_err`, `_prec_scale`, `_env`, `_prec_anp` (+ `_eta_le`, `_prec_int`); `lwMomentExp_rep` → part A `BAMomentExpGen_rep` |
| `LWMomentExp` §10 `:1286-1432`, §11 `:1433-1439` | §5 `BAMomentExp_pin_gen`, `baMomExpFarPin_holds`, `baMomExpNearPin_holds`; §6 `BALWMomentExpOfAnp`, `baLWMomentExp_of_anp` |
| `LWMomentExp` §12 `:1440-1508`; `AuxGraphRooted` §5 | §7 (instances); the nested form has no twin: `lwAuxNestedOwnOn_holds` at `BAShadowPG o.Q` |
**Input table of targets 6-9, `file:line` on the base `5c4c3362`** (script `inputs.py`):
BALWMoment Graph/BAMomentGen.lean:146; BAMomentGen_decay Graph/BAMomentGen.lean:651; BAMomentGen_Psi_facts Graph/BAMomentGen.lean:500; BAMomentGen_entry_whp Graph/BAMomentGen.lean:540; BAMomentGen_prec_of_whp Graph/BAMomentGen.lean:165; BAMomentGen_whp_of_prec Graph/BAMomentGen.lean:179; BAMomentGen_Wneg_le Graph/BAMomentGen.lean:283; BAMomentGen_L_le_W Graph/BAMomentGen.lean:311; BAMomentGen_tail_le Graph/BAMomentGen.lean:223; BAMomentGen_scalingSize_le Graph/BAMomentGen.lean:195; BAMomentGen_logW_ge Graph/BAMomentGen.lean:784; BAMomentGen_D Graph/BAMomentGen.lean:335; BAMomentGen_mem_mol_self Graph/BAMomentGen.lean:731; BAMomentGen_cont_term Graph/BAMomentGen.lean:1196; baLWMomentOfAnp_closed Graph/BAMomentExpGen.lean:189; ba_localregularXP Graph/BAProvB.lean:1104; BAWExp.prod Graph/BAProv.lean:166; baProv_bridge Graph/BAProv.lean:707; baLocRegConcl_upto5 Graph/BALocReg2B.lean:367; baZetaExpClaim_holds Graph/BAZetaExp.lean:325; baGbyZeta_holds Graph/BAAuxGraph2B.lean:623; lwAuxNestedOwnOn_holds Graph/AuxGraphRooted.lean:457; lwMomentExp_PinN Graph/LWMomentExp.lean:573; lwMomentExp_pinN_far Graph/LWMomentExp.lean:584; lwMomentExp_pinN_near Graph/LWMomentExp.lean:626; lwMomentExp_valOn_floor Graph/LWMomentExp.lean:692; lwMomentExp_valOn_smul Graph/LWMomentExp.lean:715; lwMomentExp_rad Graph/LWMomentExp.lean:738; lwMomentExp_arith Graph/LWMomentExp.lean:780; lwMomentExp_phi_zero Graph/LWMomentExp.lean:469; lwMomentExp_floor_le Graph/LWMomentExp.lean:824; lwMomentExp_logW Graph/LWMomentExp.lean:1024; lwMomentExp_comb Graph/LWMomentExp.lean:167; BAExp14a_int_slice Graph/BAExp14aB.lean:702; BAExp14a_cont_lwG Graph/BAExp14aB.lean:685; BAExp14a_det_iff Graph/BAExp14a.lean:58; BAExp14a_prec_integral Graph/BAExp14a.lean:163; BAExp14a_G_le Graph/BAExp14a.lean:1273; BAExp14a_eta_pos Graph/BAExp14a.lean:1266; BAExp14c_eta_le_one Graph/BAExp14c.lean:712; BAExp14d_Bctl_small Graph/BAExp14dB.lean:74; lwN_prec_mono Graph/LWTermExpN.lean:42; lwN_Wneg_le Graph/LWTermExpN.lean:355; lwN_tailW_le Graph/LWTermExpN.lean:121; lwN_size_rpow_neg_le Graph/LWTermExpN.lean:340; lwTail32 Graph/LWXiExp.lean:81; lwXiRad_holds Graph/AuxGraph2.lean:1241; LWPhiB_psiAll Graph/LWPsi.lean:417; lwMEA_loss Graph/LWMomentExpA.lean:270; lwMEA_phiB_sq_le Graph/LWMomentExpA.lean:213; lwMEA_prec_mono Graph/LWMomentExpA.lean:71; lwMEA_assm Graph/LWMomentExpA.lean:127; BAMomentGen_consts Graph/BAMomentGen.lean:364; baGtoAGT_holds Graph/BAExp14d.lean:307; BAMomentExpGen_rep Graph/BAMomentExpGen.lean:361; BAMomentExp_wt Graph/BAMomentExpGen.lean:345; BAMomentExp_pvalW_claim Graph/BAMomentExpGen.lean:281; BAMomentExp_scalemole Graph/BAMomentExpGen.lean:304; BAGtoAGTRooted Graph/BAMomentExpGen.lean:861; baGtoAGTRooted_holds Graph/BAMomentExpGen.lean:887; LWfgD_baFMz Graph/BAMomentExpGen.lean:112; LWfg_split Graph/BAMomentExpGen.lean:145

**Target statements, extracted from the file by script** (`line`, signature on one line, cut at 165 characters; the wrapper statements in full):
```
 146 def BAMomExpNoExp (d : ℕ) (K : ℝ) : Prop
 160 def BAMomExpNoExpOfMoment (d : ℕ) : Prop
 165 theorem baMomExpNoExp_of_moment : ∀ d : ℕ, BAMomExpNoExpOfMoment d
 263 theorem BAMomentExp_integrable (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) (p : ℕ) (Dm : Finset (Zd d (sz.L n …[278 chars]
 319 theorem BAMomentExp_LWfgD_zero (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) (h1 : (0 : ℝ) ≤ BAflowT0 sz z n) (Dm : Finset (Zd d (sz.L n))) (ω : sz.SeqΩ) (x y : …[228 chars]
 348 theorem BAMomentExp_expand {p : ℕ} (hp : Even p) (n : ℕ) {outs : List (BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p))))} (hW : ∀ o ∈ outs, p ≤ o.Q.g.waved.countP …[516 chars]
 978 def BAMomentExpOn (d : ℕ) (dom : ∀ (L : ℕ) [NeZero L], Zd d L → Zd d L → ℝ → Finset (Zd d L)) (reg : ∀ (sz : Sizes d) (n : ℕ), ℝ → ℝ → Idx d (sz.L n) (sz.W n) × Idx  …[199 chars]
 992 def BAMomExpFarPin (d : ℕ) (K : ℝ) : Prop
 996 def BAMomExpNearPin (d : ℕ) (K : ℝ) : Prop
1002 theorem BAMomentExp_pin_gen {d : ℕ} {K : ℝ} (hK : 0 < K) (dom : ∀ (L : ℕ) [NeZero L], Zd d L → Zd d L → ℝ → Finset (Zd d L)) (hPin : 3 ≤ d → ∀ {p q : ℕ}, 0 < p → ∀ Γ …[317 chars]
1117 theorem baMomExpFarPin_holds (d : ℕ) {K : ℝ} (hK : 0 < K) : BAMomExpFarPin d K
1123 theorem baMomExpNearPin_holds (d : ℕ) {K : ℝ} (hK : 0 < K) : BAMomExpNearPin d K
1141 def BAMomentExpOfParts (d : ℕ) : Prop
1146 theorem baMomentExp_of_parts (d : ℕ) : BAMomentExpOfParts d
1202 def BALWMomentExpOfAnp (d : ℕ) : Prop
1207 theorem baLWMomentExp_of_anp : ∀ d : ℕ, BALWMomentExpOfAnp d
```
```
160:def BAMomExpNoExpOfMoment (d : ℕ) : Prop := BALWMoment d → ∀ K : ℝ, 0 < K → BAMomExpNoExp d K
1202:def BALWMomentExpOfAnp (d : ℕ) : Prop := BAAnpAuxG d → BALWMomentExp d
def BAMomentExpOfParts (d : ℕ) : Prop :=
  ∀ K : ℝ, 0 < K → BAMomExpNoExp d K → BAMomExpFarPin d K → BAMomExpNearPin d K → BALWMomentExp d
```
**Statement diff against `T2483_*`.** `T2483b_eq.lean` = the check file's Part 2 (the shapes of targets 6 and 8 turned into `def Shape6`, `def Shape8` by script) + `import RBM3D.Graph.BAMomentExpGenB` + the `match_*` theorems below:
```
$ python3 -I stmt_diff_b.py T2483b_eq.lean ; lake env lean T2483b_eq.lean ; echo exit   ->  eq exit=0 ; error lines: 0
theorem match_6a : Shape6 ↔ ∀ d : ℕ, BAMomExpNoExpOfMoment d := Iff.rfl
theorem match_6b : Shape6 := baMomExpNoExp_of_moment
theorem match_8 : Shape8 ↔ ∀ (d : ℕ) (dom : ∀ (L : ℕ) [NeZero L], Zd d L → Zd d L → ℝ → Finset (Zd d L))
    (reg : ∀ (sz : Sizes d) (n : ℕ), ℝ → ℝ → Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) → Prop), BAMomentExpOn d dom reg := Iff.rfl
theorem match_9a : ∀ d, T2483_MomentExpOfAnp d ↔ BALWMomentExpOfAnp d := fun d => Iff.rfl
theorem match_9b : T2483_MomentExp := baLWMomentExp_of_anp
theorem match_9c : ∀ d, T2483_BALWMomentExp d ↔ BALWMomentExp d := fun d => Iff.rfl
```
Target 9 (`T2483_MomentExpOfAnp`, `T2483_MomentExp`) and part A's `T2483_BALWMomentExp` equal the Lean statements up to the name (`Iff.rfl`); the shapes of targets 6 (`Shape6`) and 8 (`Shape8`) equal `BAMomExpNoExpOfMoment` and `BAMomentExpOn` up to the unfolding of `LWfgD` (`Iff.rfl`).

**Compiled nonempty instances** (12 `example`s in the file; data of (a′) (1); every deterministic hypothesis discharged; left as hypotheses: `STInitialGT2gL`, `LWLoopExpgL`, `BAAnpAuxG 3`):
```
ex 1 line 1245 example (n : ℕ) : Nonempty {_q : Idx 3 (sz0.L n) (sz0.W n) × | /-- **Instance of the index sets**: the index set of the target (pairs with `λ²/L² < 1 - t`)
ex 2 line 1248 example (K : ℝ) (hK : 0 < K) (n : ℕ) : | /-- **Instance of the index sets**: the index set of the target (pairs with `λ²/L² < 1 - t`)
ex 3 line 1258 example : Nonempty {q : Idx 3 (sz0.L 0) (sz0.W 0) × Idx 3 (s | 
ex 4 line 1288 example (hAnp : BAAnpAuxG 3) (hI : STInitialGT2gL (baFMz sz0 | /-- **Instance (i) of target 9** (`baLWMomentExp_of_anp`): at `d = 3`, `p = 2`, the data abo
ex 5 line 1294 example (hAnp : BAAnpAuxG 3) (hI : STInitialGT2gL (baFMz sz0 | /-- **Instance of target 6** (`baMomExpNoExp_of_moment`): regime (A) at `K = 6`, `d = 3`, `p
ex 6 line 1301 example (hI : STInitialGT2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 | /-- **Instance of target 8** (the far and the two near pins at `K = 1/100`, `d = 3`, `p = 2`
ex 7 line 1306 example (hI : STInitialGT2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 | /-- **Instance of target 8** (the far and the two near pins at `K = 1/100`, `d = 3`, `p = 2`
ex 8 line 1311 example (hI : STInitialGT2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 | 
ex 9 line 1317 example (hAnp : BAAnpAuxG 3) (hI : STInitialGT2gL (baFMz sz0 | /-- **Instance of the assembly** (`baMomentExp_of_parts`) at `d = 3`, `K = 1/100`, with the 
ex10 line 1326 example : ∃ outs errs : List (BAProvOut (baPG (BAGraph.ofLGr | /-- **Instance of target 7** (`BAMomentExp_expand`) at `d = 3`, `n = 0` (`L = 4`, `W = 32`),
ex11 line 1334 example : Integrable (fun ω => ‖LWfgD (baFMz sz0 zSeq) 0 (1  | /-- **Instances of the integrability and of `t = 0`** at the same data: `|f^{Dm}_{xy}|²` is 
ex12 line 1337 example (ω : sz0.SeqΩ) : LWfgD (baFMz sz0 zSeq) 0 0 ω {0} 0  | /-- **Instances of the integrability and of `t = 0`** at the same data: `|f^{Dm}_{xy}|²` is 
examples: 12
```
Index sets: target 9's `{q // λ²/L² < 1 - t}` (every `n`), regime (A)'s (every `K > 0`, every `n`: the diagonal pair) and the three pins' `¬ regA` (`K = 1/100`, `n = 0`: `x = 0`, `y = (32,32,32)`) are nonempty (ex 1-3). Target 7 (ex 10) has no hypothesis left (`Dm = {0}`, 1 of 64 blocks).

**Premise-scan probe** (why target 6 is stated through `BAMomExpNoExpOfMoment`): a theorem with the hypothesis `BALWMoment d` puts the unproved `BALWMoment` into the scan, and the full-library `#assert_rbm_axioms` fails:
```
theorem scanTestFoo (d : ℕ) (h : BALWMoment d) : True := trivial   -- scratch file, then #assert_rbm_axioms
scan_test.lean:7:0: error: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`, `s …
[RBM.BA.BALWMoment]
```

**UBA-C1 table** (R1 not used: no `gK`, no `Sizes` read beyond the pin vocabulary):
| targets | `sz.lam` read | coupling `g₀` read | crossing |
|---|---|---|---|
| 6, 8, 9 | pin vocabulary only: regime `λ²/L² < 1 - t`, `sfT`, `ellT`, `Bparam`/`Bctl`/`LWPhiB`; `0 < λ ≤ 𝔡⁻¹` from `WO` (window of `LWPhiB`) | `g₀ = BAflowLam0 sz z n` only as `0 < g₀ ≤ 𝔡⁻¹` into `baGtoAGTRooted_holds` | none |
| 7 | none | `BAlwData` at `(g0, E, t, m)` of the merged `BAWExp.prod`, `BAReal` | none |
**Hypothesis table** (premise → band discharge → BA discharge): `BALWMoment d` (6) → `lwMoment_holds` → inside `BAMomExpNoExpOfMoment`, supplied in 9 by `baLWMomentOfAnp_closed`; `BAAnpAuxG d` (9) → `lwAnp_holds` → antecedent of `BALWMomentExpOfAnp` (L3d1);
`LWAssmExpgL` (6, 8) → `LWAssmExp` → inside the statement defs, converted to `LWAssmgL` for `LWPhiB` by `BAMomentExpGenB_assm` (`BAExp14d_Bctl_small`, `lwN_prec_mono`, `LWPhiB_psiAll`); `STInitialGT2gL`, `LWLoopExpgL` → other gates' pins → hypotheses of the instances;
`hPin` of `BAMomentExp_pin_gen` → `lwMomentExp_PinN` → proved by the model-free `lwMomentExp_pinN_far/near`; path binder → none (discharged in part A); `BAFlow`, `0 ≤ t ≤ BAflowT0` → `STFlow`, `lemT` → `flow_sz0`, `half_lt_t0` at the instances.

**Greps (ticket acceptance):**
```
$ clash.sh   # git grep -wE of the 16 new public names over every local and remote ref except t/T2483b
refs scanned: 496 (main 94e626a1); refs with a hit: 6
refs with a hit: main, t/T2473c, t/T2483, t/T2485, t/T2487, origin/main; every hit is the line `RBM3D/Graph/BAMomentExpGen.lean:50` (a docstring of part A naming `BALWMomentExpOfAnp`); no declaration
$ grep -nE "sz\.lam|withLam|Sizes|gK" RBM3D/Graph/BAMomentExpGenB.lean | wc -l  ->  76 lines: sz.lam 31, withLam 22 (the law of the pin), Sizes 43 (type, namespace, seqP), gK 2 (only the hypothesis name hlgK)
statement-level sz.lam hits: lines 151 154 984 988 (the regime and sfT of the pin text in BAMomExpNoExp, BAMomentExpOn); the other sz.lam hits are in proofs and hypotheses of private lemmas (reason: UBA-C1 table)
$ grep -c BAShapePath RBM3D/Graph/BAMomentExpGenB.lean  ->  0   ; BAAnpAuxG in code: statement def line 1202, instances at lines 1288 1294 1317 
$ git diff main...t/T2483b --stat | tail -2  ->   RBM3D/Graph/BAMomentExpGenB.lean | 1344 ++++++++++++++++++++++++++++++++++++++ ;  1 file changed, 1344 insertions(+)   [merge-base 772b1ca1 = L3d2b-1]
$ grep -rln "import RBM3D.Graph.BAMomentExpGenB" RBM3D RBM3D.lean | wc -l  ->  0   (RBM1D/RBM2D: nothing ported, no diff-stat)
```

**Narrative.**
- *Target 6 is stated through a wrapper.* The ticket's shape `∀ d, BALWMoment d → ∀ K, 0 < K → BAMomExpNoExp d K` as a theorem puts `BALWMoment` into the premise scan (probe above); `BAMomExpNoExpOfMoment d := BALWMoment d → ∀ K, 0 < K → BAMomExpNoExp d K`
  is that statement (`match_6a` is `Iff.rfl`), the device of `BALWMomentOfAnp`. The proof is the band's: `BALWMoment` at the window `ε₁` of `BAMomentExpGenB_assm`, `Φ_B(c r)² ≤ C_c e^{√(K (log W)^{3/2})} 𝖳_t(r ∧ ℓ)²`, loss `N^{o(1)}`.
- *Target 7* (`BAMomentExp_expand`) has no integrability hypothesis (unlike `BAMomentGen_expand`): `BAWExp.prod` gives a sum of integrals and `BAExp14a_int_slice` transports each continuous integrand (`BAMomentExpGenB_cont_valW`); `|Wt| ≤ 1` and the weight are part A's.
- *Target 8* (`BAMomentExp_pin_gen`): per output of `ba_localregularXP` (`p`, `c = ε₁/2`, `K0 = ⌈1/𝔠⌉`, `D = (D+1)/𝔠`): errors by the weighted size bound; `inl (ext 1) ∈ mol (inl (ext 0))` by the scale-mole tail; the rest by the rooted G3
  (`baGtoAGTRooted_holds` with `rep` from `BAMomentExpGen_rep`), the nested form at the shadow (`lwAuxNestedOwnOn_holds`, premise `(BAShadowPG o.Q).LocReg345 p` from `baLocRegConcl_upto5`), `ζ = baZetaVar` (`baZetaExpClaim_holds`, `baGbyZeta_holds`) with
  `ρ = (2K+1)(log W)^{3/2}`, and the model-free pin; then `≺ → 𝔼` (`BAExp14a_prec_integral`), `lwMoment_sum_det`, `BAMomentExp_expand`. The exponent `nM` of the shadow graph is transported by `x ^ (BAShadowPG o.Q).g.nM = x ^ o.Q.g.nM` (`BAGraph.shadow_nM`).
- *Target 9*: `baMomentExp_of_parts` (exact split `LWfg_split`, `E|f|^p ≤ 3^{p-1} Σ E|f^•|^p`) at `K = 1`; `baLWMomentExp_of_anp` composes `baLWMomentOfAnp_closed`, `baMomExpNoExp_of_moment`, the far and near pins; `BAAnpAuxG` stays the antecedent of the statement def.
- *Scope.* No merged file is edited, no `private` is deleted (`open private` of `lwMEA_*`, `lwMomentExp_comb`, `BASizeClaim_sizeConst_nonneg`); no new structure or inductive; private helpers carry the stem `BAMomentExpGenB_`. One `set_option maxHeartbeats 3200000` (the band twin has the same limit).
  Nothing is ported from `../RBM1D` or `../RBM2D` (twins of merged RBM3D files only; nothing there was read or run).
- The band lemma `lwMomentExp_prec_anp` carries a hypothesis `hreg2` (`K (log W)^{3/2} ℓ_t < |a-b|`) that its proof does not use; the BA private twin omits it.

## (c) Verified Mathlib names (`env.contains` on the 107 names used in the file, `names_chk.lean`: 107 present, 0 absent; one line per namespace)
`(root)`: `integral_complex_ofReal`, `abs_of_nonneg`, `abs_of_pos`, `continuous_finsetSum`, `div_le_iff₀`, `div_le_self`, `div_lt_iff₀`, `div_pow`, `even_iff_two_dvd`, `inv_anti₀`, `inv_le_iff_one_le_mul₀'`, `inv_nonneg`, `le_add_of_nonneg_left`, `le_add_of_nonneg_right`, `le_mul_of_one_le_left`, `le_mul_of_one_le_right`, `mul_div_cancel₀`, `mul_le_mul_of_nonneg_left`, `mul_le_mul_of_nonneg_right`, `mul_pow`, `neg_nonpos`, `norm_mul`, `norm_pow`, `norm_sub_le`, `norm_sum_le`, `one_le_inv_iff₀`, `one_le_mul_of_one_le_of_one_le`, `one_le_pow₀`, `pow_le_one₀`, `pow_le_pow_left₀`, `pow_le_pow_of_le_one`, `pow_le_pow_right₀`, `pow_mul`, `sub_nonneg`, `tendsto_rpow_atTop`
`Complex`: `Complex.im_le_norm`, `Complex.norm_real`
`Filter`: `Filter.tendsto_atTop_mono'`
`Finset`: `Finset.card_le_univ`, `Finset.card_univ`, `Finset.mem_filter`, `Finset.prod_const`, `Finset.sum_div`, `Finset.sum_eq_zero`, `Finset.sum_le_sum`, `Finset.sum_nonneg`
`Fintype`: `Fintype.card`, `Fintype.card_fin`, `Fintype.card_fun`, `Fintype.card_piFinset`, `Fintype.piFinset`
`Int`: `Int.toNat_of_nonneg`
`List`: `List.countP_le_length`, `List.le_sum_of_mem`, `List.map_append`, `List.map_congr_left`, `List.mem_append`, `List.mem_map_of_mem`, `List.sum_le_sum`, `List.sum_map_mul_left`
`MeasureTheory`: `MeasureTheory.Integrable.of_bound`, `MeasureTheory.integral_add`, `MeasureTheory.integral_congr_ae`, `MeasureTheory.integral_const`, `MeasureTheory.integral_const_mul`, `MeasureTheory.integral_mono_of_nonneg`, `MeasureTheory.integral_nonneg`, `MeasureTheory.integral_zero`
`Nat`: `Nat.cast_le`, `Nat.cast_nonneg`, `Nat.cast_pos`, `Nat.cast_pow`, `Nat.cast_zero`, `Nat.eq_zero_or_pos`, `Nat.floor_natCast`, `Nat.le_ceil`, `Nat.le_mul_of_pos_left`, `Nat.le_mul_of_pos_right`, `Nat.one_le_cast`, `Nat.pow_le_pow_left`
`Real`: `Real.abs_le_sqrt`, `Real.exp`, `Real.exp_le_exp`, `Real.log`, `Real.log_nonneg`, `Real.log_pos`, `Real.log_pow`, `Real.log_two_gt_d9`, `Real.log_two_lt_d9`, `Real.norm_eq_abs`, `Real.norm_of_nonneg`, `Real.one_le_rpow`, `Real.rpow_add`, `Real.rpow_add_one`, `Real.rpow_le_one_of_one_le_of_nonpos`, `Real.rpow_le_rpow`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_mul`, `Real.rpow_natCast`, `Real.rpow_nonneg`, `Real.rpow_one`, `Real.rpow_pos_of_pos`, `Real.self_le_rpow_of_one_le`, `Real.sqrt`, `Real.sqrt_eq_rpow`, `Real.sqrt_le_sqrt`
`ZMod`: `ZMod.card`
Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
- Conditional results (CLAUDE.md §5.6): `baLWMomentExp_of_anp` is `BAAnpAuxG d → BALWMomentExp d` (L3d1's pin as the antecedent), not the unconditional `lem:LW_moment_exp`; `baMomExpNoExp_of_moment` is conditional on `BALWMoment d`; `baMomExpFarPin_holds` and `baMomExpNearPin_holds` are unconditional (for every `K > 0`; `LWAssmExpgL` is a hypothesis inside their statements, as in the band)
  and `baMomentExp_of_parts` takes (A), the far pin and the near pins as the antecedents of its statement def (all three are proved here, (A) from `BALWMoment`).
- Open: `T2483_MomentExpClosed` (`∀ d, BALWMomentExp d`) is not proved: it needs L3d1's `BAAnpAuxG`; the first consumer written after L3d1 merges (L5, L40-F2) proves it from `baLWMomentExp_of_anp`. The root import line `import RBM3D.Graph.BAMomentExpGenB` is the hub's.
- Finding (no content change): the ticket's non-binding shape of target 6 is realized through the wrapper `BAMomExpNoExpOfMoment` (premise scan, probe above); the pinned `T2483_*` statements of this part (target 9) equal the Lean statements.
- `T2483c` (`7_8:1653`, `B:428-431`; proof-internal): the BA edge variables `ζ` of `(eq:Gbyxi2_BA)` need `ρ - 2R ≥ K' log W` for every `K'`; with `R = K (log W)^{3/2}` the radius is `ρ = (2K+1)(log W)^{3/2}` (the band proof has `ρ = 2R + 1`).
  The window `ε₁ = min(ε₀, d c₀/4)` (`c₀ = min(2𝔠𝔡, ε)/2` in the proof of `BAExp14d_Bctl_small`, `Bctl ≤ 2 N^{-c₀}`) replaces the band's `min(ε₀, d c/2)`; no statement differs.
- No `T2483_*` content changed; no finding against the ticket beyond the wrapper.
