Auditor model: claude-opus-5-5

# T2378 audit (BA-DGE, design of stages G and E, report only) — round 1

Written Sat Oct 10 11:13:05 UTC 2026. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2378-audit1`, detached at `t/T2378` = `f2c609a`.
Inputs: ticket, `docs/reports/T2378-design.md`, `docs/reports/T2378-prove.md`, probe `RBM3D/Probe/T2378Pins.lean`.
Acceptance (ticket, CONTROL H173): GE1–GE6 answered with evidence; probe builds; standard axioms; no forbidden tokens; diff = probe; report-only merge, probe stays on the branch.

## 1. Scope, sizes, forbidden tokens

```
$ git diff --stat main...HEAD
 RBM3D/Probe/T2378Pins.lean | 367 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 367 insertions(+)
$ git diff main...HEAD --name-only | grep -v '^RBM3D/Probe/T2378Pins.lean$'   -> (no output, exit 1)
$ grep -nwE "sorry|admit|axiom|native_decide" RBM3D/Probe/T2378Pins.lean      -> (no output, exit 1)
$ wc -l RBM3D/Probe/T2378Pins.lean docs/reports/T2378-design.md docs/reports/T2378-prove.md
     367 RBM3D/Probe/T2378Pins.lean          (limit 400)
     199 docs/reports/T2378-design.md        (limit 300)
     295 docs/reports/T2378-prove.md         (limit 300)
$ head -1 docs/reports/T2378-prove.md
Prover model: claude-sonnet-5-5
```
The design report lives in the main worktree (CLAUDE.md §2 step 2), so the branch diff lists only the probe: the sole writable files are respected. No frozen signature touched (only a new probe file).

## 2. Build and axioms (audit worktree)

```
$ lake build RBM3D.Probe.T2378Pins        # error/warning lines filtered: no `error`, no warning in Probe/T2378Pins
✔ [3778/3778] Built RBM3D.Probe.T2378Pins (4.5s)
Build completed successfully (3778 jobs).
$ lake env lean RBM3D/Probe/T2378Pins.lean   -> exit=0, no output
$ lake env lean audit/ax.lean                # #print axioms of the 17 theorems of the probe
'RBM.Probe.T2378.BAGt_eq_green' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2378.ba_G_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2378.ba_M_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2378.ba_av_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2378.inst_BAGbEXP' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2378.BAMfine_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2378.BAMfine_block_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2378.BALDEin_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2378.BAFlow_not_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2378.BAuKer_eq_one_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2378.BAuKer_convex' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2378.AI_fastDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2378.inst_BAEKSumDecay1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2378.inst_BAMfine_block_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2378.inst_ba_M_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2378.inst_BALDEin_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2378.inst_BAuKer_convex' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Declaration count: `grep -cE "^(theorem|def|abbrev|example)"` = 32 (31 named + 1 anonymous `example`, line 326), matching the report's "31 declarations" (B2).

## 3. Statement: the stage-G target and its instance

Ticket GE2: target in the shape of the three owed pins, BA carrier, event form. Script check (`audit/stmt.lean`, exit 0, no errors):
```
example (d : ℕ) : RBM.Probe.T2378.BAGbEXP d ↔ (BAGbEXPii d ∧ BAGbEXPij d ∧ BAGbEXPav d) := Iff.rfl   -- compiles
example : SizesInst.sz0.L 0 = 4 ∧ SizesInst.sz0.W 0 = 32 := by refine ⟨?_, ?_⟩ <;> simp [SizesInst.sz0]   -- compiles
FlowPinsInst.flow_sz0 : BAFlow SizesInst.sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) FlowPinsInst.zSeq
'RBM.BA.FlowPinsInst.flow_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
```
- The target is the merged owed pins unchanged (`BA/Step1Boot.lean:108-123`, registry `Test/Axioms.lean:187-189`); event form `indMax … W^{-ε₀}` in `BAGiiGEX`/`BAGijGEX` (`Step1Boot.lean:79-94`). No re-pinning, no hidden structure field.
- `inst_BAGbEXP` (probe 99-111): hypothesis `BAGbEXP 3` (the owed pin, another gate's output, allowed); every deterministic hypothesis discharged at `d = 3`, `sz0` (`L 0 = 4`, `W 0 = 32`), `flow_sz0` (merged, standard axioms), `κ = 1/2`, `ε = 𝔡 = ε₀ = 1/10`, `𝔠 = 1/6`, `t ≡ 1/2 ≤ T₀` (`half_lt_t0`). Nondegenerate.
- `BAGavLGEX` window: `ba_av_window` (probe 87) exhibits `Ψ = W^{-1}` in `[W^{-3/2}, W^{-1/10}]` at `sz0`: the `av` pin is not vacuous at the instance's `ε₀`.
- E pins (probe 208-250) against the band pins (`Evolution/Pins.lean:64-140`, read): same quantifier order `(d n Λ κ) → ∃ C → ∀ L g W ε D s t E m σ A`, same losses/exponents (`W^{Cε}`, `ℓ_t²/ℓ_s²`, `^n` / `^(n-1)`, `W^{-D+C}`), same side conditions (`4 ≤ W^ε`, `log L ≤ W^ε`, `L^d ≤ W^K`); `‖m‖ = 1 ∧ κ ≤ Im m` replaced by `BAReal d L g κ E m`, the antecedents `Prop5Decay/5Short/6Diff1/8ZeroMode` dropped because the BA versions are merged (`baProp5s_holds` `BA/Prop5Short.lean:667`, etc.). These are design proposals, not acceptance targets; `inst_BAEKSumDecay1` (probe 301) instantiates one at `L = 4`, `n = 2`, `σ = (+,-)`, `s = 0`, `t = 1/2`, `W = 16`, `ε = 1/2`, `D = 2`, `A = δ₀` with every deterministic hypothesis discharged. The other four E pins and `BALDEin` are not instantiated (ticket asks for "one concrete instance"): observation O2.

## 4. Gap reporting (GE2/GE3): verified against the TeX

```
$ grep -n "Lemma 6.1 in" paper/tex/7_8_light_weight.tex
1948:This lemma was proved as Lemma 6.1 in \cite{RBSO1D} under the condition $\ilambda\le W^{-\e}$ for a small constant $\e>0$. The same arguments, however, apply verbatim to our setting with the bounds in \eqref{Mbound_AO} and \eqref{Mbound_AO2}.
$ grep -n RBSO1D paper/tex/Jun.bib   -> 168:@article{RBSO1D,     (bibliography entry only; no text of L6.1 in the repo)
```
- **F2** (range): `BAFlow_not_small` (probe 183) compiles with standard axioms: the merged `BAFlow` instance `GreenSchurInst.inst_BAFlow` (`BA/GreenSchur.lean:542`, read) has `λ ≡ 1/100`, violating `λ ≤ W^{-ε₁}` eventually for every `ε₁ > 0`. The design reports the gap and does **not** pin around it (ticket GE2 requirement met).
- **F1** (shape): `(GijGEX_BA)` at `7_8:1940-1946` (read: deterministic `Φ_t(a,b)`, all pairs, weights `e^{-c_λ(|a'-a|+|b'-b|)}`) vs `FlowFM.gexRHS` (`Step1Boot.lean:59-66`, read: radius-1 window, `W^{-d}1_{|a-b|≤1}`). Difference confirmed. Already partially recorded as D570 (T2256a–d, `docs/paper-deltas.md:1529`); the design adds candidates T2378a/b.
- E (`A:88-122` read): `(eq:decompUalt)`, `(Xi_infint)` with `(eq:WardM)` for BA, `(eq:decayXi)` with `Mbound_AO(2)` for BA: the BA case is written into the paper's E proofs, supporting "complete paper argument" for E1–E3. `BAuKer_convex` (probe 264) compiles, supporting F4.

## 5. GE1–GE6 coverage, with spot checks of the evidence

| item | answered in design | audit check |
|---|---|---|
| GE1 | §1: per-file R/G/T/X/H+I table, segment list `a-b:C`, group route (in place A,C,D,E,F; twin B), 30 G1 names | `wc -l` of the 22 `Green/` files = 28199, of the 6 `Evolution/` files = 4164 (match §1 totals). Classes are stated as a reading, not compiled (said in §1) |
| GE2 | §2: target, instance, BA data-fact table with merged sources, F1, F2, G2 pin `BALDEin` | 25 cited `file:line` sites printed (§6 below): all land on the named declaration |
| GE3 | §3: per-item table; G: no complete argument, design-gate 1a for G3a,G3b,G4,G5a,G5c; E: complete | consistent with §4 above |
| GE4 | §4: no stage-K/L/TUV input; waves; E3 waits for T2379 shape | grep below |
| GE5 | §5: 31 declarations, 12-row table lo/central/hi with measured ratios incl. stage-K 1.14×, exponent table, instances | probe builds, §2–§3 |
| GE6 | §6: 12 rows (G 9, E 3); T central 9.5k (10.6k with group B), reasons file by file; flag 18 | arithmetic 1.5 × 12 = 18 |

```
$ grep -nE "𝒦|KboundgL|STKbound|BAKbound|Kbound" Green/*.lean Evolution/{XiPins,SumDecay,SumDecayZero,Nonzero,Pins,Prec}.lean
Green/GbEXP.lean:835:third clause of `lem_GbEXP`, and `STKbound`, `STLK`, `STLocalMax` at `s` of Step 1.  Every
Green/GbEXP.lean:970:discharged; `STKbound`, `STLK`, `STLocalMax` at `s` are other gates' pins (the ST-6 chain).  Both
Green/GbEXP.lean:972:private theorem gbEXP_inst_stStep1 (hK : STKbound sz0 (STflowE z0))
$ grep -rln BAWinBulk --include='*.lean' RBM3D | grep -v Probe
Test/Axioms.lean BA/Step1.lean BA/Step1Fam.lean BA/Step1Boot.lean BA/Step1Trivial.lean BA/CouplingWindow.lean
$ grep -rn BAGbEXPav --include='*.lean' RBM3D | grep -v Probe/
Test/Axioms.lean:189 … ; BA/Step1Boot.lean:123:def BAGbEXPav (d : ℕ) : Prop :=
```
(matches GE4 "only `Green/GbEXP.lean:835, 970, 972`", GE2 "coupling window used only by `BA/Step1*`", and "`BAGbEXPav` has no consumer").

## 6. Citation spot check (script: `sed -n <line>p`, first 110 chars)

```
BA/GreenSchur.lean:542   theorem inst_BAFlow : BAFlow GreenSchur_szF (9 / 10) (1 / 2) (1 / 9) (1 / 2) GreenSchur_zF := by
BA/GreenSchur.lean:219   theorem BAGt_sub_BAMfine {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (ht : t < 1)
BA/GreenSchur.lean:59    theorem BAflow_real {d : ℕ} (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ) (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
BA/GreenSchur.lean:72    theorem BAflow_lam0_window {d : ℕ} (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ) (h : BAFlow sz κ ε 𝔠 𝔡 z) :
BA/GreenSchur.lean:124   theorem BAMfine_decay (d : ℕ) (hd : 0 < d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) (sz : Sizes d)
BA/GreenSchur.lean:265   theorem BAPsiI_inBlock (d L W : ℕ) [NeZero L] [NeZero W] (x y : Idx d L W)
BA/GreenSchur.lean:293   theorem green_diag_split {ι β : Type} [Fintype ι] [DecidableEq ι] [DecidableEq β] (b : ι → β)
BA/GreenSchur.lean:335   theorem green_off_split {ι β : Type} [Fintype ι] [DecidableEq ι] [DecidableEq β] (b : ι → β)
BA/FlowPins.lean:546     def BAFlow (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) : Prop :=
BA/FlowPins.lean:550     def baFMz (z : ℕ → ℂ) : FlowFM sz := baFM sz (BAflowLam0 sz z) (BAflowEs sz z)
BA/Step1.lean:576        theorem baBootstrap'_holds (d : ℕ) : BAFlowMember d → BAGbEXPii d → BAGbEXPij d → BABootstrap' d := by
BA/Step1Fam.lean:695     theorem baStep1_holds (d : ℕ) : BAGbEXPii d → BAGbEXPij d → BAStep1 d := fun hii hij =>
Green/LDE.lean:1099      theorem stochDom_normSq_Hflow_diag {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {t : ℕ → ℝ}
Green/RowIndep.lean:1237 theorem stochDom_rowSum_general (hu : 0 ≤ u)
Green/EntryCore.lean:406 def GoodEvent (G : Matrix n n ℂ) (m : ℂ) (δ : ℝ) : Prop :=
Green/FlucVanish.lean:813 noncomputable def greenDiagCentered {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ)
BA/KKernel.lean:124      theorem BAK_row_sum (g E : ℝ) (m : ℂ) (h : BASelf d L g (E : ℂ) m) (a : Zd d L) :
BA/MFixedPoint.lean:285  theorem BAt0_lt_one {z m : ℂ} (hz : 0 < z.im) (hm : 0 < m.im) : BAt0 z m < 1 := by
BA/CouplingWindow.lean:799 def BAWinBulk (sz : Sizes d) (z : ℕ → ℂ) (c₁ κ : ℝ) : Prop :=
Gauss/BlockAnderson.lean:83 def seqHflowBA (lam0 : ℕ → ℝ) (n : ℕ) (u : ℝ) (ω : SeqΩ sz) :
BA/Prop5Short.lean:667   theorem baProp5s_holds (d : ℕ) (Λ κ : ℝ) : BAProp5s d Λ κ := by
BA/CombesThomas.lean:562 theorem baPropM_holds (d : ℕ) (Λ κ : ℝ) : BAPropM d Λ κ := by
Loop/GLoopFlow.lean:64   theorem ztOf_im (m : ℂ) (E t : ℝ) : (ztOf m E t).im = etaOf m t := by
BA/Ward.lean:89          theorem BAMB_diag_eq (g : ℝ) (z m : ℂ) (h : BASelf d L g z m) (a : Zd d L) :
BA/Ward.lean:136         theorem BAm_norm_le_one (g : ℝ) (z m : ℂ) (hz : 0 ≤ z.im) (h : BASelf d L g z m) : ‖m‖ ≤ 1 := by
```

## 7. Paper-delta coverage

Proposed in design §7: `T2378a` (`BAGijGEX` band shape vs `(GijGEX_BA)`), `T2378b` (`BAGiiGEX` vs `(GiiGEX_BA)`), `T2378c` (L6.1 cited for `g ≤ W^{-ε}`, claimed for `g ≤ 𝔡⁻¹`: paper gap), `T2378d` (route remark). The E pins' side conditions reuse existing entries (`docs/paper-deltas.md`: D33 T2016a `log L ≤ W^ε`, D34 T2016b `4 ≤ W^ε`, D37 T2016e loss-free nonzero, D45 T2042a `L^d ≤ W^K`); the event form of the G pins is D539/D570. Every probe/paper difference is covered.

## 8. Verdict

**PASS** (design ticket, report-only merge; probe `RBM3D/Probe/T2378Pins.lean` stays on `t/T2378`).
- Statement: target = the three merged owed pins (`Iff.rfl`, §3); no pin around the F2 gap.
- No vacuity/hidden hypothesis/cycle: probe depends only on merged modules; `BAFlow_not_small` and the `av` window are compiled witnesses.
- Instances: `inst_BAGbEXP`, `inst_BAEKSumDecay1` plus four further instances, nondegenerate (`L = 4`, `W = 32` / `W = 16`).
- Build exit 0, standard axioms only, no forbidden tokens, diff = the probe.
- GE1–GE6 answered with file:line and script output.

The decisions listed in design §7 (F1 re-pin or keep, F2 range or external input, design-gate 1a for G3a/G3b/G4/G5a/G5c, flag 18) are the content of the opening REQ the ticket prescribes (supervisor). They are not a precondition of this report-only merge, so this audit does not ask for dispatcher sign-off.

Observations (no RETURN):
- O1. GE1 classes R/G/T are a manual reading of statements (the report says so); the line totals are reproduced, the per-segment classes are not independently re-derived here.
- O2. Of the probe pins, only `BAGbEXP` and `BAEKSumDecay1` are instantiated (plus `BALDEin_diag`, not the full `BALDEin`). The proving tickets for E1–E3 and G2 must each carry their own compiled instance.
- O3. The prover's scratch scripts (`ge1rows.py`, `rows.py`) are outside the repository: B6/B7 cannot be re-run from the repo.
